
module BinOp
{
  use ServerConfig;
  
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use ServerErrorStrings;
  use Logging;
  use Message;
  use BitOps;

  use ArkoudaBigIntCompat;
  use ArkoudaMathCompat;

  private config const logLevel = ServerConfig.logLevel;
  private config const logChannel = ServerConfig.logChannel;
  const omLogger = new Logger(logLevel, logChannel);

  /*
    Helper function to ensure that floor division cases are handled in accordance with numpy
  */
  inline proc floorDivisionHelper(numerator: ?t, denom: ?t2): real {
    if (numerator == 0 && denom == 0) || (isInf(numerator) && (denom != 0 || isInf(denom))){
      return nan;
    }
    else if (numerator > 0 && denom == -inf) || (numerator < 0 && denom == inf){
      return -1:real;
    }
    else {
      return floor(numerator/denom);
    }
  }

  /*
    Helper function to ensure that mod cases are handled in accordance with numpy
  */
  inline proc modHelper(dividend: ?t, divisor: ?t2): real {
    extern proc fmod(x: real, y: real): real;

    var res = fmod(dividend, divisor);
    // to convert fmod (truncated) results into mod (floored) results
    // when the dividend and divsor have opposite signs,
    // we add the divsor into the result
    // except for when res == 0 (divsor even divides dividend)
    // see https://en.wikipedia.org/wiki/Modulo#math_1 for more information
    if res != 0 && (((dividend < 0) && (divisor > 0)) || ((dividend > 0) && (divisor < 0))) {
      // we do + either way because we want to shift up for positive divisors and shift down for negative
      res += divisor;
    }
    return res;
  }

  enum opCategory {
    bitwiseLogic,
    bitwiseShift,
    bitwiseRot,
    comparison,
    basicArithmetic,
    fancyArithmetic,
    trueDivision
  }

  const bitwiseLogicOps: domain(string) = {"|", "&", "^"},
        bitwiseShiftOps: domain(string) = {"<<", ">>"},
        bitwiseRotOps: domain(string) = {"<<<", ">>>"},
        comparisonOps: domain(string) = {"==", "!=", "<", ">", "<=", ">="},
        basicArithmeticOps: domain(string) = {"+", "-", "*"},
        fancyArithmeticOps: domain(string) = {"//", "%", "**"};

  /*
    Get the category of an operator string

    This procedure assumes that the operator has already been validated,
    (it will not throw an error if the operator is not valid)
  */
  private proc getOpCategory(op: string): opCategory {
    if bitwiseLogicOps.contains(op) then return opCategory.bitwiseLogic;
    if bitwiseShiftOps.contains(op) then return opCategory.bitwiseShift;
    if bitwiseRotOps.contains(op) then return opCategory.bitwiseRot;
    if comparisonOps.contains(op) then return opCategory.comparison;
    if basicArithmeticOps.contains(op) then return opCategory.basicArithmetic;
    if fancyArithmeticOps.contains(op) then return opCategory.fancyArithmetic;
    else return opCategory.trueDivision;
  }

  /*
    check if an operator string matches one of the valid operators
  */
  proc isValidOperator(op: string): bool {
    return bitwiseLogicOps.contains(op) || bitwiseShiftOps.contains(op) ||
           bitwiseRotOps.contains(op) || comparisonOps.contains(op) ||
           basicArithmeticOps.contains(op) || fancyArithmeticOps.contains(op) ||
           op == "/";
  }

  private proc computeBigintMaxSize(max_bits: int): (bool, bigint) {
    const has_max_bits = max_bits != -1;
    var max_size = 1:bigint;
    if has_max_bits {
      max_size <<= max_bits;
      max_size -= 1;
    }
    return (has_max_bits, max_size);
  }

  /*
    Execute a binary operation between two scalar pdarrays according Numpy's rules

    :arg l: the array for the left hand side of the operation
    :arg r: the array for the right hand side of the operation
    :arg e: the array to store the result of the operation in
    :returns: a bool indicating whether ``et`` = ``lt`` ``op`` ``rt`` follows Numpy's operator/promotion rules
              if ``false`` an error should be thrown by the caller
              if ``true`` the operation can be considered successful
  */
  proc doBinOpvv(const ref l: [] ?lt, const ref r: [] ?rt, ref e: [] ?et, op: string) : bool {
    select getOpCategory(op) {
      when opCategory.bitwiseLogic {
        if et != commonType(lt, rt) {
          return false;
        } else if (isIntegralType(lt) || lt == bool ) && (isIntegralType(rt) || rt == bool) {
          select op {
            when "|" do e = l | r;
            when "&" do e = l & r;
            when "^" do e = l ^ r;
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.bitwiseShift {
        // shifts that result in real/complex result types are not supported
        if et != commonType(lt, rt, true) || isRealType(et) || isComplexType(et) {
          return false;
        } else if isIntegralType(lt) && isIntegralType(rt) {
          select op {
            when "<<" do lBitShift(e, l, r, et, et);
            when ">>" do rBitShift(e, l, r, et, et);
            otherwise halt("unreachable");
          }
          return true;
        } else if lt == bool && isIntegralType(rt) {
          select op {
            when "<<" do lBitShift(e, l, r, int(8), rt);
            when ">>" do rBitShift(e, l, r, int(8), rt);
            otherwise halt("unreachable");
          }
          return true;
        } else if isIntegralType(lt) && rt == bool {
          select op {
            when "<<" do lBitShift(e, l, r, lt, int(8));
            when ">>" do rBitShift(e, l, r, lt, int(8));
            otherwise halt("unreachable");
          }
          return true;
        } else if lt == bool && rt == bool {
          select op {
            when "<<" do lBitShift(e, l, r, int(8), int(8));
            when ">>" do rBitShift(e, l, r, int(8), int(8));
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.bitwiseRot {
        if et != commonType(lt, rt) {
          return false;
        } else if isIntegralType(lt) && isIntegralType(rt) {
          select op {
            when "<<<" do e = rotl(l, r);
            when ">>>" do e = rotr(l, r);
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.comparison {
        if et != bool {
          return false;
        } else if ((isIntegralType(lt) || lt == bool) && (isIntegralType(rt) || rt == bool)) ||
           (isRealType(lt) && isRealType(rt))
        {
          select op {
            when "==" do e = l == r;
            when "!=" do e = l != r;
            when "<" do e = l < r;
            when ">" do e = l > r;
            when "<=" do e = l <= r;
            when ">=" do e = l >= r;
            otherwise halt("unreachable");
          }
          return true;
        } else if (isIntegralType(lt) || lt == bool) && isRealType(rt) {
          select op {
            when "==" do e = l:rt == r;
            when "!=" do e = l:rt != r;
            when "<" do e = l:rt < r;
            when ">" do e = l:rt > r;
            when "<=" do e = l:rt <= r;
            when ">=" do e = l:rt >= r;
            otherwise halt("unreachable");
          }
          return true;
        } else if isRealType(lt) && (isIntegralType(rt) || rt == bool) {
          select op {
            when "==" do e = l == r:lt;
            when "!=" do e = l != r:lt;
            when "<" do e = l < r:lt;
            when ">" do e = l > r:lt;
            when "<=" do e = l <= r:lt;
            when ">=" do e = l >= r:lt;
            otherwise halt("unreachable");
          }
          return true;
        } else if (SupportsComplex64 || SupportsComplex128) && (
            (isComplexType(lt) && (isIntegralType(rt) || rt == bool || isRealType(rt))) ||
            ((isIntegralType(lt) || lt == bool || isRealType(lt)) && isComplexType(rt))
          ) {
          // following numpy's implementation of complex comparisons, only consider the real part
          select op {
            when "==" do e = l:real == r:real;
            when "!=" do e = l:real != r:real;
            when "<" do e = l:real < r:real;
            when ">" do e = l:real > r:real;
            when "<=" do e = l:real <= r:real;
            when ">=" do e = l:real >= r:real;
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.basicArithmetic {
        if et != commonType(lt, rt) {
          return false;
        } else if lt == bool && rt == bool {
          return false;
        } else {
          select op {
            when "+" do e = l:et + r:et;
            when "-" do e = l:et - r:et;
            when "*" do e = l:et * r:et;
            otherwise halt("unreachable");
          }
          return true;
        }
      }
      when opCategory.fancyArithmetic {
        if et != commonType(lt, rt, true) then return false;

        const lCast = if lt == bool then l:int(8) else l,
              rCast = if rt == bool then r:int(8) else r;

        if (isSignedIntegerType(lCast.eltType) && isSignedIntegerType(rCast.eltType)) ||
           (isUnsignedIntegerType(lCast.eltType) && isUnsignedIntegerType(rCast.eltType))
        {
          select op {
            when "//" do
              e = [(li, ri) in zip(lCast, rCast)] if ri != 0 then li/ri else 0;
            when "%" do
              e = [(li, ri) in zip(lCast, rCast)] if ri != 0 then li%ri else 0;
            when "**" {
              if || reduce (r < 0) {
                // use a real computation if working with negative exponents
                e = (lCast:real**rCast:real):et;
              } else {
                e = lCast**rCast;
              }
            }
            otherwise halt("unreachable");
          }
          return true;
        } else if (isSignedIntegerType(lCast.eltType) && isUnsignedIntegerType(rCast.eltType)) ||
                  (isUnsignedIntegerType(lCast.eltType) && isSignedIntegerType(rCast.eltType))
        {
          select op {
            when "//" do
              e = [(li, ri) in zip(lCast, rCast)] floorDivisionHelper(li:real, ri:real):et;
            when "%" do
              e = [(li, ri) in zip(lCast, rCast)] modHelper(li:real, ri:real):et;
            when "**" do return false;
            otherwise halt("unreachable");
          }
        } else if (isSignedIntegerType(lCast.eltType) && isRealType(rCast.eltType)) ||
                  (isRealType(lCast.eltType) && isSignedIntegerType(rCast.eltType)) ||
                  (isRealType(lCast.eltType) && isRealType(rCast.eltType))
        {
          select op {
            when "//" do e = [(li, ri) in zip(lCast, rCast)] floorDivisionHelper(li, ri):et;
            when "%" do e = [(li, ri) in zip(lCast, rCast)] modHelper(li, ri):et;
            when "**" do e = lCast**rCast;
            otherwise halt("unreachable");
          }
          return true;
        } else if (isUnsignedIntegerType(lCast.eltType) && isRealType(lCast.eltType)) ||
                  (isRealType(lCast.eltType) && isUnsignedIntegerType(lCast.eltType))
        {
          select op {
            when "//" do e = [(li, ri) in zip(lCast, rCast)] floorDivisionHelper(li, ri):et;
            when "%" do e = [(li, ri) in zip(lCast, rCast)] modHelper(li, ri):et;
            when "**" do e = lCast:et**rCast:et;
            otherwise halt("unreachable");
          }
          return true;
        } else if (SupportsComplex64 || SupportsComplex128) && (
                    (isComplexType(lt) && (isIntegralType(rt) || rt == bool || isRealType(rt))) ||
                    ((isIntegralType(lt) || lt == bool || isRealType(lt)) && isComplexType(rt)) ||
                    (isComplexType(lt) && isComplexType(rt))
                  )
        {
          select op {
            when "/" do e = lCast:et / rCast:et;
            when "//" do return false;
            when "%" do return false;
            when "**" do e = lCast:et**rCast:et;
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.trueDivision {
        if et != divType(lt, rt) {
          return false;
        } else {
          const lCast = if lt == bool then l:int(8) else l,
                rCast = if rt == bool then r:int(8) else r;

          if isIntegralType(lCast.eltType) && isIntegralType(rCast.eltType) {
            e = lCast:real / rCast:real;
          } else if (isRealType(lCast.eltType) && isRealType(rCast.eltType)) ||
                    (isRealType(lCast.eltType) && isSignedIntegerType(rCast.eltType)) ||
                    (isSignedIntegerType(lCast.eltType) && isRealType(rCast.eltType))
          {
            e = lCast / rCast;
          } else {
            e = lCast:et / rCast:et;
          }

          return true;
        }
      }
      otherwise halt("unreachable");
    }
    return false; // here to make the compiler happy
  }

  private proc lBitShift(ref e, const ref l, const ref r, type leftCast, type rightCast) {
    // [(ei, li, ri,) in zip(l, r, e)] ei = if ri < 64 && ri >= 0 then li << ri else 0;
    forall (li, ri, ei) in zip(l:leftCast, r:rightCast, e)
      do ei = if ri < 64 && ri >= 0 then li << ri else 0;
  }

  private proc rBitShift(ref e, const ref l, const ref r, type leftCast, type rightCast) {
    // [(ei, li, ri,) in zip(l, r, e)] ei = if ri < 64 && ri >= 0 then li >> ri else 0;
    forall (li, ri, ei) in zip(l:leftCast, r:rightCast, e)
      do ei = if ri < 64 && ri >= 0 then li >> ri else 0;
  }

  /*
    Execute a binary operation between two scalar pdarrays where at least one of the operands is a bigint

    :arg l: the array for the left hand side of the operation
    :arg r: the array for the right hand side of the operation
    :arg e: the array to store the result of the operation in
    :returns: a bool indicating whether ``et`` = ``lt`` ``op`` ``rt`` follows Numpy's operator/promotion rules
              if ``false`` an error should be thrown by the caller
              if ``true`` the operation can be considered successful
  */
  proc doBinOpvvBigint(const ref l: [] ?lt, const ref r: [] ?rt, ref e: [] ?et, op: string, max_bits: bigint): bool throws {
    if isRealType(lt) || isComplexType(lt) ||
       isRealType(rt) || isComplexType(rt)
        then return false;

    const (has_max_bits, max_size) = computeBigintMaxSize(max_bits);

    // copy l into e
    // allows more memory efficient op= operations to be used below
    e = if lt == bigint then l else l:bigint;

    select getOpCategory(op) {
      when opCategory.bitwiseLogic {
        // bitwise ops are only supported between two bigints
        if lt == bigint && rt == bigint {
          select op {
            when "|" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                ei |= ri;
                if has_max_bits then ei &= lms;
              }
            }
            when "&" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                ei &= ri;
                if has_max_bits then ei &= lms;
              }
            }
            when "^" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                ei ^= ri;
                if has_max_bits then ei &= lms;
              }
            }
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.trueDivision {
        // true division is only supported between two bigints
        if lt == bigint && rt == bigint {
          forall (ei, ri) in zip(e, r) with (var lms = max_size) {
            ei /= ri;
            if has_max_bits then ei &= lms;
          }
        } else {
          return false;
        }
      }
      when opCategory.bitwiseShift {
        if lt == bigint && (rt == bigint || isIntegralType(rt)) {
          select op {
            when "<<" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                if has_max_bits {
                  if ri >= max_bits {
                    ei = 0;
                  } else {
                    ei <<= ri;
                    ei &= lms;
                  }
                } else {
                  ei <<= ri;
                }
              }
            }
            when ">>" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                if has_max_bits {
                  if ri >= max_bits {
                    ei = 0;
                  } else {
                    rightShiftEq(ei, ri); // ei >>= ri;
                    ei &= lms;
                  }
                } else {
                  rightShiftEq(ei, ri); // ei >>= ri;
                }
              }
            }
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.bitwiseRot {
        if lt == bigint && (rt == bigint || isIntegralType(rt)) {
          const leftCpy = l;
          select op {
            when "<<<" {
              if !has_max_bits then throw new Error("<<< requires max_bits to be set");
              forall (ei, li, ri) in zip(e, leftCpy, r) with (var lms = max_size, var lmb = max_bits) {
                const moddedShift = if isSignedIntegerType(rt) then ri % lmb else ri % lmb:uint;
                ei <<= moddedShift;
                const shiftAmt = if isSignedIntegerType(rt) then lmb - moddedShift else lmb:uint - moddedShift;
                rightShiftEq(li, shiftAmt);
                ei += li;
                ei &= lms;
              }
            }
            when ">>>" {
              if !has_max_bits then throw new Error(">>> requires max_bits to be set");
              forall (ei, li, ri) in zip(e, leftCpy, r) with (var lms = max_size, var lmb = max_bits) {
                const moddedShift = if isSignedIntegerType(rt) then ri % lmb else ri % lmb:uint;
                rightShiftEq(ei, moddedShift);
                const shiftAmt = if isSignedIntegerType(rt) then lmb - moddedShift else lmb:uint - moddedShift;
                li <<= shiftAmt;
                ei += li;
                ei &= lms;
              }
            }
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.fancyArithmetic {
        if lt == bigint && (rt == bigint || isIntegralType(rt)) {
          select op {
            when "//" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                if ri == 0 {
                  ei = 0:bigint;
                } else {
                  ei /= ri;
                  if has_max_bits then ei &= lms;
                }
              }
            }
            when "%" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                if ri == 0 {
                  ei = 0:bigint;
                } else {
                  ei %= ri;
                  if has_max_bits then ei &= lms;
                }
              }
            }
            when "**" {
              if || reduce (r < 0)
                then throw new Error("Attempt to exponentiate base of type BigInt to negative exponent");
              if has_max_bits {
                forall (ei, ri) in zip(e, r) with (var lms = max_size) do
                  powMod(ei, ei, ri, lms+1);
              } else {
                forall (ei, ri) in zip(e, r) do
                  ei **= ri:uint;
              }
            }
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
      when opCategory.basicArithmetic {
        if (lt == bigint && rt == bigint) ||
           (lt == bigint && (isIntegralType(rt) || rt == bool)) ||
           (rt == bigint && (isIntegralType(lt) || lt == bool))
        {
          select op {
            when "+" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                ei += ri;
                if has_max_bits then ei &= lms;
              }
            }
            when "-" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                ei -= ri;
                if has_max_bits then ei &= lms;
              }
            }
            when "*" {
              forall (ei, ri) in zip(e, r) with (var lms = max_size) {
                ei *= ri;
                if has_max_bits then ei &= lms;
              }
            }
            otherwise halt("unreachable");
          }
          return true;
        } else {
          return false;
        }
      }
    }
    return false;
  }

  proc doBigintBinOpvvCmp(const ref l: [] ?lt, const ref r: [] ?rt, ref e: [] bool, op: string): bool {
    if isRealType(lt) || isComplexType(lt) ||
       isRealType(rt) || isComplexType(rt)
        then return false;

    select op {
      when "==" do e = l == r;
      when "!=" do e = l != r;
      when "<" do e = l < r;
      when ">" do e = l > r;
      when "<=" do e = l <= r;
      when ">=" do e = l >= r;
      otherwise halt("unreachable");
    }
    return true;
  }

  /*
  Generic function to execute a binary operation on pdarray entries 
  in the symbol table

  :arg l: symbol table entry of the LHS operand

  :arg r: symbol table entry of the RHS operand

  :arg e: symbol table entry to store result of operation

  :arg op: string representation of binary operation to execute
  :type op: string

  :arg rname: name of the `e` in the symbol table
  :type rname: string

  :arg pn: routine name of callsite function
  :type pn: string

  :arg st: SymTab to act on
  :type st: borrowed SymTab 

  :returns: (MsgTuple) 
  :throws: `UndefinedSymbolError(name)`
  */
  proc doBinOpvvOld(l, r, e, op: string, rname, pn, st) throws {
    if e.etype == bool {
      // Since we know that the result type is a boolean, we know
      // that it either (1) is an operation between bools or (2) uses
      // a boolean operator (<, <=, etc.)
      if l.etype == bool && r.etype == bool {
        select op {
          when "|" {
            e.a = l.a | r.a;
          }
          when "&" {
            e.a = l.a & r.a;
          }
          when "^" {
            e.a = l.a ^ r.a;
          }
          when "==" {
            e.a = l.a == r.a;
          }
          when "!=" {
            e.a = l.a != r.a;
          }
          when "<" {
            e.a = l.a:int < r.a:int;
          }
          when ">" {
            e.a = l.a:int > r.a:int;
          }
          when "<=" {
            e.a = l.a:int <= r.a:int;
          }
          when ">=" {
            e.a = l.a:int >= r.a:int;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      }
      // All types support the same binary operations when the resultant
      // type is bool and `l` and `r` are not both boolean, so this does
      // not need to be specialized for each case.
      else {
        if ((l.etype == real && r.etype == bool) || (l.etype == bool && r.etype == real)) {
          select op {
            when "<" {
              e.a = l.a:real < r.a:real;
            }
            when ">" {
              e.a = l.a:real > r.a:real;
            }
            when "<=" {
              e.a = l.a:real <= r.a:real;
            }
            when ">=" {
              e.a = l.a:real >= r.a:real;
            }
            when "==" {
              e.a = l.a:real == r.a:real;
            }
            when "!=" {
              e.a = l.a:real != r.a:real;
            }
            otherwise {
              var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
              return new MsgTuple(errorMsg, MsgType.ERROR);
            }
          }
        }
        else {
          select op {
            when "<" {
              e.a = l.a < r.a;
            }
            when ">" {
              e.a = l.a > r.a;
            }
            when "<=" {
              e.a = l.a <= r.a;
            }
            when ">=" {
              e.a = l.a >= r.a;
            }
            when "==" {
              e.a = l.a == r.a;
            }
            when "!=" {
              e.a = l.a != r.a;
            }
            otherwise {
              var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
              return new MsgTuple(errorMsg, MsgType.ERROR); 
            }
          }
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    // Since we know that both `l` and `r` are of type `int` and that
    // the resultant type is not bool (checked in first `if`), we know
    // what operations are supported based on the resultant type
    else if (l.etype == int && r.etype == int) ||
            (l.etype == uint && r.etype == uint)  {
      if e.etype == int || e.etype == uint {
        select op {
          when "+" {
            e.a = l.a + r.a;
          }
          when "-" {
            e.a = l.a - r.a;
          }
          when "*" {
            e.a = l.a * r.a;
          }
          when "//" { // floordiv
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] ei = if ri != 0 then li/ri else 0;
          }
          when "%" { // modulo
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] ei = if ri != 0 then li%ri else 0;
          }
          when "<<" {
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] if ri < 64 then ei = li << ri;
          }                    
          when ">>" {
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] if ri < 64 then ei = li >> ri;
          }
          when "<<<" {
            e.a = rotl(l.a, r.a);
          }
          when ">>>" {
            e.a = rotr(l.a, r.a);
          }
          when "&" {
            e.a = l.a & r.a;
          }                    
          when "|" {
            e.a = l.a | r.a;
          }                    
          when "^" {
            e.a = l.a ^ r.a;
          }
          when "**" { 
            if || reduce (r.a<0){
              //instead of error, could we paste the below code but of type float?
              var errorMsg = "Attempt to exponentiate base of type Int64 to negative exponent";
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);  
              return new MsgTuple(errorMsg, MsgType.ERROR);                                
            }
            e.a= l.a**r.a;
          }     
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
            return new MsgTuple(errorMsg, MsgType.ERROR); 
          }
        }
      } else if e.etype == real {
        select op {
          // True division is the only integer type that would result in a
          // resultant type of `real`
          when "/" {
            e.a = l.a:real / r.a:real;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
            return new MsgTuple(errorMsg, MsgType.ERROR); 
          }   
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if (e.etype == int && r.etype == uint) ||
            (e.etype == uint && r.etype == int) {
      select op {
        when ">>" {
          ref ea = e.a;
          ref la = l.a;
          ref ra = r.a;
          [(ei,li,ri) in zip(ea,la,ra)] if ri < 64 then ei = li >> ri;
        }
        when "<<" {
          ref ea = e.a;
          ref la = l.a;
          ref ra = r.a;
          [(ei,li,ri) in zip(ea,la,ra)] if ri < 64 then ei = li << ri;
        }
        when ">>>" {
          e.a = rotr(l.a, r.a);
        }
        when "<<<" {
          e.a = rotl(l.a, r.a);
        }
        otherwise {
          var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
          omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
          return new MsgTuple(errorMsg, MsgType.ERROR);
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if (l.etype == uint && r.etype == int) ||
              (l.etype == int && r.etype == uint) {
      select op {
        when "+" {
          e.a = l.a:real + r.a:real;
        }
        when "-" {
          e.a = l.a:real - r.a:real;
        }
        when "/" { // truediv
            e.a = l.a:real / r.a:real;
        }
        when "//" { // floordiv
          ref ea = e.a;
          var la = l.a:real;
          var ra = r.a:real;
          [(ei,li,ri) in zip(ea,la,ra)] ei = floorDivisionHelper(li, ri);
        }
        otherwise {
          var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
          omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
          return new MsgTuple(errorMsg, MsgType.ERROR); 
        }   
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    // If either RHS or LHS type is real, the same operations are supported and the
    // result will always be a `real`, so all 3 of these cases can be shared.
    else if ((l.etype == real && r.etype == real) || (l.etype == int && r.etype == real)
             || (l.etype == real && r.etype == int)) {
      select op {
          when "+" {
            e.a = l.a + r.a;
          }
          when "-" {
            e.a = l.a - r.a;
          }
          when "*" {
            e.a = l.a * r.a;
          }
          when "/" { // truediv
            e.a = l.a / r.a;
          } 
          when "//" { // floordiv
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] ei = floorDivisionHelper(li, ri);
          }
          when "**" { 
            e.a= l.a**r.a;
          }
          when "%" {
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] ei = modHelper(li, ri);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((l.etype == uint && r.etype == real) || (l.etype == real && r.etype == uint)) {
      select op {
          when "+" {
            e.a = l.a:real + r.a:real;
          }
          when "-" {
            e.a = l.a:real - r.a:real;
          }
          when "*" {
            e.a = l.a:real * r.a:real;
          }
          when "/" { // truediv
            e.a = l.a:real / r.a:real;
          } 
          when "//" { // floordiv
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] ei = floorDivisionHelper(li, ri);
          }
          when "**" { 
            e.a= l.a:real**r.a:real;
          }
          when "%" {
            ref ea = e.a;
            ref la = l.a;
            ref ra = r.a;
            [(ei,li,ri) in zip(ea,la,ra)] ei = modHelper(li, ri);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((l.etype == int && r.etype == bool) || (l.etype == bool && r.etype == int)) {
      select op {
          when "+" {
            // Since we don't know which of `l` or `r` is the int and which is the `bool`,
            // we can just cast both to int, which will be a noop for the vector that is
            // already `int`
            e.a = l.a:int + r.a:int;
          }
          when "-" {
            e.a = l.a:int - r.a:int;
          }
          when "*" {
            e.a = l.a:int * r.a:int;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((l.etype == uint && r.etype == bool) || (l.etype == bool && r.etype == uint)) {
      select op {
          when "+" {
            e.a = l.a:uint + r.a:uint;
          }
          when "-" {
            e.a = l.a:uint - r.a:uint;
          }
          when "*" {
            e.a = l.a:uint * r.a:uint;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);  
    } else if ((l.etype == real && r.etype == bool) || (l.etype == bool && r.etype == real)) {
      select op {
          when "+" {
            e.a = l.a:real + r.a:real;
          }
          when "-" {
            e.a = l.a:real - r.a:real;
          }
          when "*" {
            e.a = l.a:real * r.a:real;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    var errorMsg = notImplementedError(pn,l.dtype,op,r.dtype);
    omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
    return new MsgTuple(errorMsg, MsgType.ERROR);
  }

  proc doBinOpvs(l, val, e, op: string, dtype, rname, pn, st) throws {
    if e.etype == bool {
      // Since we know that the result type is a boolean, we know
      // that it either (1) is an operation between bools or (2) uses
      // a boolean operator (<, <=, etc.)
      if l.etype == bool && val.type == bool {
        select op {
          when "|" {
            e.a = l.a | val;
          }
          when "&" {
            e.a = l.a & val;
          }
          when "^" {
            e.a = l.a ^ val;
          }
          when "==" {
            e.a = l.a == val;
          }
          when "!=" {
            e.a = l.a != val;
          }
          when "<" {
            e.a = l.a:int < val:int;
          }
          when ">" {
            e.a = l.a:int > val:int;
          }
          when "<=" {
            e.a = l.a:int <= val:int;
          }
          when ">=" {
            e.a = l.a:int >= val:int;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      }
      // All types support the same binary operations when the resultant
      // type is bool and `l` and `r` are not both boolean, so this does
      // not need to be specialized for each case.
      else {
        if ((l.etype == real && val.type == bool) || (l.etype == bool && val.type == real)) {
          select op {
            when "<" {
              e.a = l.a:real < val:real;
            }
            when ">" {
              e.a = l.a:real > val:real;
            }
            when "<=" {
              e.a = l.a:real <= val:real;
            }
            when ">=" {
              e.a = l.a:real >= val:real;
            }
            when "==" {
              e.a = l.a:real == val:real;
            }
            when "!=" {
              e.a = l.a:real != val:real;
            }
            otherwise {
              var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
              return new MsgTuple(errorMsg, MsgType.ERROR);
            }
          }
        }
        else {
          select op {
            when "<" {
              e.a = l.a < val;
            }
            when ">" {
              e.a = l.a > val;
            }
            when "<=" {
              e.a = l.a <= val;
            }
            when ">=" {
              e.a = l.a >= val;
            }
            when "==" {
              e.a = l.a == val;
            }
            when "!=" {
              e.a = l.a != val;
            }
            otherwise {
              var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
              return new MsgTuple(errorMsg, MsgType.ERROR); 
            }
          }
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    // Since we know that both `l` and `r` are of type `int` and that
    // the resultant type is not bool (checked in first `if`), we know
    // what operations are supported based on the resultant type
    else if (l.etype == int && val.type == int) ||
            (l.etype == uint && val.type == uint) {
      if e.etype == int || e.etype == uint {
        select op {
          when "+" {
            e.a = l.a + val;
          }
          when "-" {
            e.a = l.a - val;
          }
          when "*" {
            e.a = l.a * val;
          }
          when "//" { // floordiv
            ref ea = e.a;
            ref la = l.a;
            [(ei,li) in zip(ea,la)] ei = if val != 0 then li/val else 0;
          }
          when "%" { // modulo
            ref ea = e.a;
            ref la = l.a;
            [(ei,li) in zip(ea,la)] ei = if val != 0 then li%val else 0;
          }
          when "<<" {
            if val < 64 {
              e.a = l.a << val;
            }
          }                    
          when ">>" {
            if val < 64 {
              e.a = l.a >> val;
            }
          }
          when "<<<" {
            e.a = rotl(l.a, val);
          }
          when ">>>" {
            e.a = rotr(l.a, val);
          }
          when "&" {
            e.a = l.a & val;
          }                    
          when "|" {
            e.a = l.a | val;
          }                    
          when "^" {
            e.a = l.a ^ val;
          }
          when "**" { 
            e.a= l.a**val;
          }     
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
            return new MsgTuple(errorMsg, MsgType.ERROR); 
          }
        }
      } else if e.etype == real {
        select op {
          // True division is the only integer type that would result in a
          // resultant type of `real`
          when "/" {
            e.a = l.a:real / val:real;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
            return new MsgTuple(errorMsg, MsgType.ERROR); 
          }
            
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if (e.etype == int && val.type == uint) ||
            (e.etype == uint && val.type == int) {
      select op {
        when ">>" {
          if val < 64 {
            e.a = l.a >> val:l.etype;
          }
        }
        when "<<" {
          if val < 64 {
            e.a = l.a << val:l.etype;
          }
        }
        when ">>>" {
          e.a = rotr(l.a, val:l.etype);
        }
        when "<<<" {
          e.a = rotl(l.a, val:l.etype);
        }
        when "+" {
          e.a = l.a + val:l.etype;
        }
        when "-" {
          e.a = l.a - val:l.etype;
        }
        otherwise {
          var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
          omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
          return new MsgTuple(errorMsg, MsgType.ERROR);
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    // If either RHS or LHS type is real, the same operations are supported and the
    // result will always be a `real`, so all 3 of these cases can be shared.
    else if ((l.etype == real && val.type == real) || (l.etype == int && val.type == real)
             || (l.etype == real && val.type == int)) {
      select op {
          when "+" {
            e.a = l.a + val;
          }
          when "-" {
            e.a = l.a - val;
          }
          when "*" {
            e.a = l.a * val;
          }
          when "/" { // truediv
            e.a = l.a / val;
          } 
          when "//" { // floordiv
            ref ea = e.a;
            ref la = l.a;
            [(ei,li) in zip(ea,la)] ei = floorDivisionHelper(li, val);
          }
          when "**" { 
            e.a= l.a**val;
          }
          when "%" {
            ref ea = e.a;
            ref la = l.a;
            [(ei,li) in zip(ea,la)] ei = modHelper(li, val);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if e.etype == real && ((l.etype == uint && val.type == int) || (l.etype == int && val.type == uint)) {
      select op {
          when "+" {
            e.a = l.a: real + val: real;
          }
          when "-" {
            e.a = l.a: real - val: real;
          }
          when "/" { // truediv
            e.a = l.a: real / val: real;
          }
          when "//" { // floordiv
            ref ea = e.a;
            var la = l.a;
            [(ei,li) in zip(ea,la)] ei = floorDivisionHelper(li, val:real);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if ((l.etype == uint && val.type == real) || (l.etype == real && val.type == uint)) {
      select op {
          when "+" {
            e.a = l.a: real + val: real;
          }
          when "-" {
            e.a = l.a: real - val: real;
          }
          when "*" {
            e.a = l.a: real * val: real;
          }
          when "/" { // truediv
            e.a = l.a: real / val: real;
          } 
          when "//" { // floordiv
            ref ea = e.a;
            ref la = l.a;
            [(ei,li) in zip(ea,la)] ei = floorDivisionHelper(li, val);
          }
          when "**" { 
            e.a= l.a: real**val: real;
          }
          when "%" {
            ref ea = e.a;
            ref la = l.a;
            [(ei,li) in zip(ea,la)] ei = modHelper(li, val);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((l.etype == int && val.type == bool) || (l.etype == bool && val.type == int)) {
      select op {
          when "+" {
            // Since we don't know which of `l` or `r` is the int and which is the `bool`,
            // we can just cast both to int, which will be a noop for the vector that is
            // already `int`
            e.a = l.a:int + val:int;
          }
          when "-" {
            e.a = l.a:int - val:int;
          }
          when "*" {
            e.a = l.a:int * val:int;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((l.etype == real && val.type == bool) || (l.etype == bool && val.type == real)) {
      select op {
          when "+" {
            e.a = l.a:real + val:real;
          }
          when "-" {
            e.a = l.a:real - val:real;
          }
          when "*" {
            e.a = l.a:real * val:real;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,l.dtype,op,dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    var errorMsg = unrecognizedTypeError(pn, "("+dtype2str(l.dtype)+","+dtype2str(dtype)+")");
    omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
    return new MsgTuple(errorMsg, MsgType.ERROR);
  }

  proc doBinOpsv(val, r, e, op: string, dtype, rname, pn, st) throws {
    if e.etype == bool {
      // Since we know that the result type is a boolean, we know
      // that it either (1) is an operation between bools or (2) uses
      // a boolean operator (<, <=, etc.)
      if r.etype == bool && val.type == bool {
        select op {
          when "|" {
            e.a = val | r.a;
          }
          when "&" {
            e.a = val & r.a;
          }
          when "^" {
            e.a = val ^ r.a;
          }
          when "==" {
            e.a = val == r.a;
          }
          when "!=" {
            e.a = val != r.a;
          }
          when "<" {
            e.a = val:int < r.a:int;
          }
          when ">" {
            e.a = val:int > r.a:int;
          }
          when "<=" {
            e.a = val:int <= r.a:int;
          }
          when ">=" {
            e.a = val:int >= r.a:int;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      }
      // All types support the same binary operations when the resultant
      // type is bool and `l` and `r` are not both boolean, so this does
      // not need to be specialized for each case.
      else {
        if ((r.etype == real && val.type == bool) || (r.etype == bool && val.type == real)) {
          select op {
            when "<" {
              e.a = val:real < r.a:real;
            }
            when ">" {
              e.a = val:real > r.a:real;
            }
            when "<=" {
              e.a = val:real <= r.a:real;
            }
            when ">=" {
              e.a = val:real >= r.a:real;
            }
            when "==" {
              e.a = val:real == r.a:real;
            }
            when "!=" {
              e.a = val:real != r.a:real;
            }
            otherwise {
              var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
              return new MsgTuple(errorMsg, MsgType.ERROR);
            }
          }
        }
        else {
          select op {
            when "<" {
              e.a = val < r.a;
            }
            when ">" {
              e.a = val > r.a;
            }
            when "<=" {
              e.a = val <= r.a;
            }
            when ">=" {
              e.a = val >= r.a;
            }
            when "==" {
              e.a = val == r.a;
            }
            when "!=" {
              e.a = val != r.a;
            }
            otherwise {
              var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
              return new MsgTuple(errorMsg, MsgType.ERROR); 
            }
          }
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    // Since we know that both `l` and `r` are of type `int` and that
    // the resultant type is not bool (checked in first `if`), we know
    // what operations are supported based on the resultant type
    else if (r.etype == int && val.type == int) ||
            (r.etype == uint && val.type == uint) {
      if e.etype == int || e.etype == uint {
        select op {
          when "+" {
            e.a = val + r.a;
          }
          when "-" {
            e.a = val - r.a;
          }
          when "*" {
            e.a = val * r.a;
          }
          when "//" { // floordiv
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = if ri != 0 then val/ri else 0;
          }
          when "%" { // modulo
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = if ri != 0 then val%ri else 0;
          }
          when "<<" {
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] if ri < 64 then ei = val << ri;
          }                    
          when ">>" {
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] if ri < 64 then ei = val >> ri;
          }
          when "<<<" {
            e.a = rotl(val, r.a);
          }
          when ">>>" {
            e.a = rotr(val, r.a);
          }
          when "&" {
            e.a = val & r.a;
          }                    
          when "|" {
            e.a = val | r.a;
          }                    
          when "^" {
            e.a = val ^ r.a;
          }
          when "**" {
            if || reduce (r.a<0){
              var errorMsg = "Attempt to exponentiate base of type Int64 to negative exponent";
              omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
              return new MsgTuple(errorMsg, MsgType.ERROR); 
            }
            e.a= val**r.a;
          }     
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
            return new MsgTuple(errorMsg, MsgType.ERROR); 
          }
        }
      } else if e.etype == real {
        select op {
          // True division is the only integer type that would result in a
          // resultant type of `real`
          when "/" {
            e.a = val:real / r.a:real;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);                              
            return new MsgTuple(errorMsg, MsgType.ERROR); 
          }
            
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if (e.etype == int && val.type == uint) ||
            (e.etype == uint && val.type == int) {
      select op {
        when ">>" {
          ref ea = e.a;
          ref ra = r.a;
          [(ei,ri) in zip(ea,ra)] if ri:uint < 64 then ei = val:r.etype >> ri;
        }
        when "<<" {
          ref ea = e.a;
          ref ra = r.a;
          [(ei,ri) in zip(ea,ra)] if ri:uint < 64 then ei = val:r.etype << ri;
        }
        when ">>>" {
          e.a = rotr(val:r.etype, r.a);
        }
        when "<<<" {
          e.a = rotl(val:r.etype, r.a);
        }
        when "+" {
          e.a = val:r.etype + r.a;
        }
        when "-" {
          e.a = val:r.etype - r.a;
        }
        otherwise {
          var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
          omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
          return new MsgTuple(errorMsg, MsgType.ERROR);
        }
      }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    // If either RHS or LHS type is real, the same operations are supported and the
    // result will always be a `real`, so all 3 of these cases can be shared.
    else if ((r.etype == real && val.type == real) || (r.etype == int && val.type == real)
             || (r.etype == real && val.type == int)) {
      select op {
          when "+" {
            e.a = val + r.a;
          }
          when "-" {
            e.a = val - r.a;
          }
          when "*" {
            e.a = val * r.a;
          }
          when "/" { // truediv
            e.a = val:real / r.a:real;
          } 
          when "//" { // floordiv
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = floorDivisionHelper(val:real, ri);
          }
          when "**" { 
            e.a= val**r.a;
          }
          when "%" {
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = modHelper(val:real, ri);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if e.etype == real && ((r.etype == uint && val.type == int) || (r.etype == int && val.type == uint)) {
      select op {
          when "+" {
            e.a = val:real + r.a:real;
          }
          when "-" {
            e.a = val:real - r.a:real;
          }
          when "/" { // truediv
            e.a = val:real / r.a:real;
          }
          when "//" { // floordiv
            ref ea = e.a;
            var ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = floorDivisionHelper(val:real, ri);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    else if ((r.etype == uint && val.type == real) || (r.etype == real && val.type == uint)) {
      select op {
          when "+" {
            e.a = val:real + r.a:real;
          }
          when "-" {
            e.a = val:real - r.a:real;
          }
          when "*" {
            e.a = val:real * r.a:real;
          }
          when "/" { // truediv
            e.a = val:real / r.a:real;
          } 
          when "//" { // floordiv
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = floorDivisionHelper(val:real, ri);
          }
          when "**" { 
            e.a= val:real**r.a:real;
          }
          when "%" {
            ref ea = e.a;
            ref ra = r.a;
            [(ei,ri) in zip(ea,ra)] ei = modHelper(val:real, ri);
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((r.etype == int && val.type == bool) || (r.etype == bool && val.type == int)) {
      select op {
          when "+" {
            // Since we don't know which of `l` or `r` is the int and which is the `bool`,
            // we can just cast both to int, which will be a noop for the vector that is
            // already `int`
            e.a = val:int + r.a:int;
          }
          when "-" {
            e.a = val:int - r.a:int;
          }
          when "*" {
            e.a = val:int * r.a:int;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    } else if ((r.etype == real && val.type == bool) || (r.etype == bool && val.type == real)) {
      select op {
          when "+" {
            e.a = val:real + r.a:real;
          }
          when "-" {
            e.a = val:real - r.a:real;
          }
          when "*" {
            e.a = val:real * r.a:real;
          }
          otherwise {
            var errorMsg = notImplementedError(pn,dtype,op,r.dtype);
            omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
            return new MsgTuple(errorMsg, MsgType.ERROR);
          }
        }
      var repMsg = "created %s".doFormat(st.attrib(rname));
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }
    var errorMsg = unrecognizedTypeError(pn, "("+dtype2str(dtype)+","+dtype2str(r.dtype)+")");
    omLogger.error(getModuleName(),getRoutineName(),getLineNumber(),errorMsg);
    return new MsgTuple(errorMsg, MsgType.ERROR);
  }

  proc doBigIntBinOpvvOld(l, r, op: string) throws {
    var max_bits = max(l.max_bits, r.max_bits);
    var max_size = 1:bigint;
    var has_max_bits = max_bits != -1;
    if has_max_bits {
      max_size <<= max_bits;
      max_size -= 1;
    }
    ref la = l.a;
    ref ra = r.a;
    var tmp = if l.etype == bigint then la else la:bigint;
    // these cases are not mutually exclusive,
    // so we have a flag to track if tmp is ever populated
    var visted = false;

    // had to create bigint specific BinOp procs which return
    // the distributed array because we need it at SymEntry creation time
    if l.etype == bigint && r.etype == bigint { // {&, |, ^, /}
      // first we try the ops that only work with
      // both being bigint
      select op {
        when "&" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t &= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "|" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t |= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "^" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t ^= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "/" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t /= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
      }
    }
    // {<<, >>, <<<, >>>, //, %, **}
    if l.etype == bigint && (r.etype == bigint || r.etype == int || r.etype == uint) {
      // then we try the ops that only work with a
      // left hand side of bigint
      if r.etype != bigint {
        // can't shift a bigint by a bigint
        select op {
          when "<<" {
            forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
              if has_max_bits {
                if ri >= max_bits {
                  t = 0;
                }
                else {
                  t <<= ri;
                  t &= local_max_size;
                }
              }
              else {
                t <<= ri;
              }
            }
            visted = true;
          }
          when ">>" {
            forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
              if has_max_bits {
                if ri >= max_bits {
                  t = 0;
                }
                else {
                  rightShiftEq(t, ri);
                  t &= local_max_size;
                }
              }
              else {
                rightShiftEq(t, ri);
              }
            }
            visted = true;
          }
          when "<<<" {
            if !has_max_bits {
              throw new Error("Must set max_bits to rotl");
            }
            var botBits = la;
            forall (t, ri, bot_bits) in zip(tmp, ra, botBits) with (var local_max_size = max_size) {
              var modded_shift = if r.etype == int then ri % max_bits else ri % max_bits:uint;
              t <<= modded_shift;
              var shift_amt = if r.etype == int then max_bits - modded_shift else max_bits:uint - modded_shift;
              rightShiftEq(bot_bits, shift_amt);
              t += bot_bits;
              t &= local_max_size;
            }
            visted = true;
          }
          when ">>>" {
            if !has_max_bits {
              throw new Error("Must set max_bits to rotr");
            }
            var topBits = la;
            forall (t, ri, tB) in zip(tmp, ra, topBits) with (var local_max_size = max_size) {
              var modded_shift = if r.etype == int then ri % max_bits else ri % max_bits:uint;
              rightShiftEq(t, modded_shift);
              var shift_amt = if r.etype == int then max_bits - modded_shift else max_bits:uint - modded_shift;
              tB <<= shift_amt;
              t += tB;
              t &= local_max_size;
            }
            visted = true;
          }
        }
      }
      select op {
        when "//" { // floordiv
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            if ri != 0 {
              t /= ri;
            }
            else {
              t = 0:bigint;
            }
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "%" { // modulo
          // we only do in place mod when ri != 0, tmp will be 0 in other locations
          // we can't use ei = li % ri because this can result in negatives
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            if ri != 0 {
              mod(t, t, ri);
            }
            else {
              t = 0:bigint;
            }
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "**" {
          if || reduce (ra<0) {
            throw new Error("Attempt to exponentiate base of type BigInt to negative exponent");
          }
          if has_max_bits {
            forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
              powMod(t, t, ri, local_max_size + 1);
            }
          }
          else {
            forall (t, ri) in zip(tmp, ra) {
              t **= ri:uint;
            }
          }
          visted = true;
        }
      }
    }
    // {+, -, *}
    if (l.etype == bigint && r.etype == bigint) ||
       (l.etype == bigint && (r.etype == int || r.etype == uint || r.etype == bool)) ||
       (r.etype == bigint && (l.etype == int || l.etype == uint || l.etype == bool)) {
      select op {
        when "+" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t += ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "-" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t -= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "*" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t *= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
      }
    }
    if !visted {
      throw new Error("Unsupported operation: " + l.etype:string +" "+ op +" "+ r.etype:string);
    }
    return (tmp, max_bits);
  }

  proc doBigIntBinOpvvBoolReturn(l, r, op: string) throws {
    select op {
      when "<" {
        return l.a < r.a;
      }
      when ">" {
        return l.a > r.a;
      }
      when "<=" {
        return l.a <= r.a;
      }
      when ">=" {
        return l.a >= r.a;
      }
      when "==" {
        return l.a == r.a;
      }
      when "!=" {
        return l.a != r.a;
      }
      otherwise {
        // we should never reach this since we only enter this proc
        // if boolOps.contains(op)
        throw new Error("Unsupported operation: " + l.etype:string +" "+ op +" "+ r.etype:string);
      }
    }
  }

  proc doBigIntBinOpvs(l, val, op: string) throws {
    var max_bits = l.max_bits;
    var max_size = 1:bigint;
    var has_max_bits = max_bits != -1;
    if has_max_bits {
      max_size <<= max_bits;
      max_size -= 1;
    }
    ref la = l.a;
    var tmp = if l.etype == bigint then la else la:bigint;
    // these cases are not mutually exclusive,
    // so we have a flag to track if tmp is ever populated
    var visted = false;

    // had to create bigint specific BinOp procs which return
    // the distributed array because we need it at SymEntry creation time
    if l.etype == bigint && val.type == bigint {
      // first we try the ops that only work with
      // both being bigint
      select op {
        when "&" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t &= local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "|" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t |= local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "^" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t ^= local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "/" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t /= local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
      }
    }
    if l.etype == bigint && (val.type == bigint || val.type == int || val.type == uint) {
      // then we try the ops that only work with a
      // left hand side of bigint
      if val.type != bigint {
        // can't shift a bigint by a bigint
        select op {
          when "<<" {
            if has_max_bits && val >= max_bits {
              forall t in tmp with (var local_zero = 0:bigint) {
                t = local_zero;
              }
            }
            else {
              forall t in tmp with (var local_val = val, var local_max_size = max_size) {
                t <<= local_val;
                if has_max_bits {
                  t &= local_max_size;
                }
              }
            }
            visted = true;
          }
          when ">>" {
            if has_max_bits && val >= max_bits {
              forall t in tmp with (var local_zero = 0:bigint) {
                t = local_zero;
              }
            }
            else {
              forall t in tmp with (var local_max_size = max_size) {
                rightShiftEq(t, val);
                if has_max_bits {
                  t &= local_max_size;
                }
              }
            }
            visted = true;
          }
          when "<<<" {
            if !has_max_bits {
              throw new Error("Must set max_bits to rotl");
            }
            var botBits = la;
            var modded_shift = if val.type == int then val % max_bits else val % max_bits:uint;
            var shift_amt = if val.type == int then max_bits - modded_shift else max_bits:uint - modded_shift;
            forall (t, bot_bits) in zip(tmp, botBits) with (var local_val = modded_shift, var local_shift_amt = shift_amt, var local_max_size = max_size) {
              t <<= local_val;
              rightShiftEq(bot_bits, local_shift_amt);
              t += bot_bits;
              t &= local_max_size;
            }
            visted = true;
          }
          when ">>>" {
            if !has_max_bits {
              throw new Error("Must set max_bits to rotr");
            }
            var topBits = la;
            var modded_shift = if val.type == int then val % max_bits else val % max_bits:uint;
            var shift_amt = if val.type == int then max_bits - modded_shift else max_bits:uint - modded_shift;
            forall (t, tB) in zip(tmp, topBits) with (var local_val = modded_shift, var local_shift_amt = shift_amt, var local_max_size = max_size) {
              rightShiftEq(t, local_val);
              tB <<= local_shift_amt;
              t += tB;
              t &= local_max_size;
            }
            visted = true;
          }
        }
      }
      select op {
        when "//" { // floordiv
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            if local_val != 0 {
              t /= local_val;
            }
            else {
              t = 0:bigint;
            }
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "%" { // modulo
          // we only do in place mod when val != 0, tmp will be 0 in other locations
          // we can't use ei = li % val because this can result in negatives
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            if local_val != 0 {
              mod(t, t, local_val);
            }
            else {
              t = 0:bigint;
            }
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "**" {
          if val<0 {
            throw new Error("Attempt to exponentiate base of type BigInt to negative exponent");
          }
          if has_max_bits {
            forall t in tmp with (var local_val = val, var local_max_size = max_size) {
              powMod(t, t, local_val, local_max_size + 1);
            }
          }
          else {
            forall t in tmp with (var local_val = val) {
              t **= local_val:uint;
            }
          }
          visted = true;
        }
      }
    }
    if (l.etype == bigint && val.type == bigint) ||
       (l.etype == bigint && (val.type == int || val.type == uint || val.type == bool)) ||
       (val.type == bigint && (l.etype == int || l.etype == uint || l.etype == bool)) {
      select op {
        when "+" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t += local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "-" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t -= local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "*" {
          forall t in tmp with (var local_val = val, var local_max_size = max_size) {
            t *= local_val;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
      }
    }
    if !visted {
      throw new Error("Unsupported operation: " + l.etype:string +" "+ op +" "+ val.type:string);
    }
    return (tmp, max_bits);
  }

  proc doBigIntBinOpvsBoolReturn(l, val, op: string) throws {
    ref la = l.a;
    var tmp = makeDistArray(la.size, bool);
    select op {
      when "<" {
        forall (t, li) in zip(tmp, la) with (var local_val = val) {
          t = (li < local_val);
        }
      }
      when ">" {
        forall (t, li) in zip(tmp, la) with (var local_val = val) {
          t = (li > local_val);
        }
      }
      when "<=" {
        forall (t, li) in zip(tmp, la) with (var local_val = val) {
          t = (li <= local_val);
        }
      }
      when ">=" {
        forall (t, li) in zip(tmp, la) with (var local_val = val) {
          t = (li >= local_val);
        }
      }
      when "==" {
        forall (t, li) in zip(tmp, la) with (var local_val = val) {
          t = (li == local_val);
        }
      }
      when "!=" {
        forall (t, li) in zip(tmp, la) with (var local_val = val) {
          t = (li != local_val);
        }
      }
      otherwise {
        // we should never reach this since we only enter this proc
        // if boolOps.contains(op)
        throw new Error("Unsupported operation: " +" "+ l.etype:string + op +" "+ val.type:string);
      }
    }
    return tmp;
  }

  proc doBigIntBinOpsv(val, r, op: string) throws {
    var max_bits = r.max_bits;
    var max_size = 1:bigint;
    var has_max_bits = max_bits != -1;
    if has_max_bits {
      max_size <<= max_bits;
      max_size -= 1;
    }
    ref ra = r.a;
    var tmp = makeDistArray(ra.size, bigint);
    tmp = val:bigint;
    // these cases are not mutually exclusive,
    // so we have a flag to track if tmp is ever populated
    var visted = false;

    // had to create bigint specific BinOp procs which return
    // the distributed array because we need it at SymEntry creation time
    if val.type == bigint && r.etype == bigint {
      // first we try the ops that only work with
      // both being bigint
      select op {
        when "&" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t &= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "|" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t |= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "^" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t ^= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "/" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t /= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
      }
    }
    if val.type == bigint && (r.etype == bigint || r.etype == int || r.etype == uint) {
      // then we try the ops that only work with a
      // left hand side of bigint
      if r.etype != bigint {
        // can't shift a bigint by a bigint
        select op {
          when "<<" {
            forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
              if has_max_bits {
                if ri >= max_bits {
                  t = 0;
                }
                else {
                  t <<= ri;
                  t &= local_max_size;
                }
              }
              else {
                t <<= ri;
              }
            }
            visted = true;
          }
          when ">>" {
            forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
              if has_max_bits {
                if ri >= max_bits {
                  t = 0;
                }
                else {
                  rightShiftEq(t, ri);
                  t &= local_max_size;
                }
              }
              else {
                rightShiftEq(t, ri);
              }
            }
            visted = true;
          }
          when "<<<" {
            if !has_max_bits {
              throw new Error("Must set max_bits to rotl");
            }
            var botBits = makeDistArray(ra.size, bigint);
            botBits = val;
            forall (t, ri, bot_bits) in zip(tmp, ra, botBits) with (var local_max_size = max_size) {
              var modded_shift = if r.etype == int then ri % max_bits else ri % max_bits:uint;
              t <<= modded_shift;
              var shift_amt = if r.etype == int then max_bits - modded_shift else max_bits:uint - modded_shift;
              rightShiftEq(bot_bits, shift_amt);
              t += bot_bits;
              t &= local_max_size;
            }
            visted = true;
          }
          when ">>>" {
            if !has_max_bits {
              throw new Error("Must set max_bits to rotr");
            }
            var topBits = makeDistArray(ra.size, bigint);
            topBits = val;
            forall (t, ri, tB) in zip(tmp, ra, topBits) with (var local_max_size = max_size) {
              var modded_shift = if r.etype == int then ri % max_bits else ri % max_bits:uint;
              rightShiftEq(t, modded_shift);
              var shift_amt = if r.etype == int then max_bits - modded_shift else max_bits:uint - modded_shift;
              tB <<= shift_amt;
              t += tB;
              t &= local_max_size;
            }
            visted = true;
          }
        }
      }
      select op {
        when "//" { // floordiv
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            if ri != 0 {
              t /= ri;
            }
            else {
              t = 0:bigint;
            }
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "%" { // modulo
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            if ri != 0 {
              mod(t, t, ri);
            }
            else {
              t = 0:bigint;
            }
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "**" {
          if || reduce (ra<0) {
            throw new Error("Attempt to exponentiate base of type BigInt to negative exponent");
          }
          if has_max_bits {
            forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
              powMod(t, t, ri, local_max_size + 1);
            }
          }
          else {
            forall (t, ri) in zip(tmp, ra) {
              t **= ri:uint;
            }
          }
          visted = true;
        }
      }
    }
    if (val.type == bigint && r.etype == bigint) ||
       (val.type == bigint && (r.etype == int || r.etype == uint || r.etype == bool)) ||
       (r.etype == bigint && (val.type == int || val.type == uint || val.type == bool)) {
      select op {
        when "+" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t += ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "-" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t -= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
        when "*" {
          forall (t, ri) in zip(tmp, ra) with (var local_max_size = max_size) {
            t *= ri;
            if has_max_bits {
              t &= local_max_size;
            }
          }
          visted = true;
        }
      }
    }
    if !visted {
      throw new Error("Unsupported operation: " + val.type:string +" "+ op +" "+ r.etype:string);
    }
    return (tmp, max_bits);
  }

  proc doBigIntBinOpsvBoolReturn(val, r, op: string) throws {
    ref ra = r.a;
    var tmp = makeDistArray(ra.size, bool);
    select op {
      when "<" {
        forall (t, ri) in zip(tmp, ra) with (var local_val = val) {
          t = (local_val < ri);
        }
      }
      when ">" {
        forall (t, ri) in zip(tmp, ra) with (var local_val = val) {
          t = (local_val > ri);
        }
      }
      when "<=" {
        forall (t, ri) in zip(tmp, ra) with (var local_val = val) {
          t = (local_val <= ri);
        }
      }
      when ">=" {
        forall (t, ri) in zip(tmp, ra) with (var local_val = val) {
          t = (local_val >= ri);
        }
      }
      when "==" {
        forall (t, ri) in zip(tmp, ra) with (var local_val = val) {
          t = (local_val == ri);
        }
      }
      when "!=" {
        forall (t, ri) in zip(tmp, ra) with (var local_val = val) {
          t = (local_val != ri);
        }
      }
      otherwise {
        // we should never reach this since we only enter this proc
        // if boolOps.contains(op)
        throw new Error("Unsupported operation: " + val.type:string +" "+ op +" "+ r.etype:string);
      }
    }
    return tmp;
  }
}
