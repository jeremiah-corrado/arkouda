module ArrayApiSpecial {
  use ServerConfig;
  use MultiTypeSymbolTable;
  use MultiTypeSymEntry;
  use Logging;
  use Message;
  use ServerErrorStrings;

  use Reflection;

  private config const logLevel = ServerConfig.logLevel;
  private config const logChannel = ServerConfig.logChannel;
  const aLogger = new Logger(logLevel, logChannel);

  @arkouda.registerND
  proc clipMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab, param nd: int): MsgTuple throws {
    param pn = Reflection.getRoutineName();
    const name = msgArgs.getValueOf("name"),
          minArg = msgArgs.get("min"),
          maxArg = msgArgs.get("max"),
          rname = st.nextName();

    var gEnt: borrowed GenSymEntry = getGenericTypedArrayEntry(name, st);

    proc clipArray(type t): MsgTuple throws {
      const minVal = minArg.getScalarValue(t),
            maxVal = maxArg.getScalarValue(t),
            eIn = toSymEntry(gEnt, t, nd);

      var eOut = st.addEntry(rname, eIn.tupShape, t);

      forall i in eOut.a.domain do
        eOut.a[i] = min(max(eIn.a[i], minVal), maxVal);

      const repMsg = "created " + st.attrib(rname);
      aLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    select gEnt.dtype {
      when DType.Int64 do return clipArray(int);
      when DType.UInt64 do return clipArray(uint);
      when DType.Float64 do return clipArray(real);
      when DType.Bool do return clipArray(bool);
      otherwise {
        var errorMsg = notImplementedError(pn,dtype2str(gEnt.dtype));
        aLogger.error(getModuleName(),pn,getLineNumber(),errorMsg);
        return new MsgTuple(errorMsg,MsgType.ERROR);
      }
    }
  }

  @arkouda.registerND
  proc clipAryMsg(cmd: string, msgArgs: borrowed MessageArgs, st: borrowed SymTab, param nd: int): MsgTuple throws {
    param pn = Reflection.getRoutineName();
    const name = msgArgs.getValueOf("name"),
          minArg = msgArgs.get("min"),
          maxArg = msgArgs.get("max"),
          rname = st.nextName();

    var gEnt: borrowed GenSymEntry = getGenericTypedArrayEntry(name, st);

    proc clipArray(type t): MsgTuple throws {
      const eIn = toSymEntry(gEnt, t, nd);
      var eOut = st.addEntry(rname, eIn.tupShape, t);

      const minArr = if hasMin then minArg.getScalarValue(t) else max(t),
            maxVal = if hasMax then maxArg.getScalarValue(t) else min(t);

      

      const repMsg = "created " + st.attrib(rname);
      aLogger.debug(getModuleName(),getRoutineName(),getLineNumber(),repMsg);
      return new MsgTuple(repMsg, MsgType.NORMAL);
    }

    select gEnt.dtype {
      when DType.Int64 do return clipArray(int, minVal, maxVal);
      when DType.UInt64 do return clipArray(uint, minVal, maxVal);
      when DType.Float64 do return clipArray(real, minVal, maxVal);
      when DType.Bool do return clipArray(bool, minVal, maxVal);
      otherwise {
        var errorMsg = notImplementedError(pn,dtype2str(gEnt.dtype));
        aLogger.error(getModuleName(),pn,getLineNumber(),errorMsg);
        return new MsgTuple(errorMsg,MsgType.ERROR);
      }
    }
  }

  proc clipHelper(ref a: [?d] ?t, const ref minArr: [] t, maxVal: t) {
    forall i in a.domain do
      a[i] = min(max(a[i], minArr[i]), maxVal);
  }

  proc clipHelper(ref a: [?d] ?t, minVal: t, const ref maxArr: [] t) {
    forall i in a.domain do
      a[i] = min(max(a[i], minVal), maxArr[i]);
  }

  proc clipHelper(ref a: [?d] ?t, const ref minArr: [] t, const ref maxArr: [] t) {
    forall i in a.domain do
      a[i] = min(max(a[i], minArr[i]), maxArr[i]);
  }
}
