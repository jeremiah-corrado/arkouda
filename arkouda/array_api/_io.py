from __future__ import annotations
from ._array_object import Array

from arkouda.client import generic_msg
from arkouda.pdarrayclass import create_pdarray


def read_hdf5(filename: str, dataset: str, rank: int, /) -> Array:
    repMsg = generic_msg(
        cmd=f"readSingleHdfArray{rank}D",
        args={
            "dset": dataset,
            "filename": filename,
        },
    )

    print(repMsg)

    return Array._new(create_pdarray(repMsg))


def lshdf(filename: str):
    repMsg = generic_msg(
        cmd="lshdf",
        args={
            "filename": filename,
        },
    )

    return repMsg
