sig ljf-certificates.
accum_sig ljf-formulas.

kind cert, index                         type.
kind choice                              type.
type left, right                       choice.

type storeL_jc                     cert -> cert -> index -> prop.
type decideL_je                    cert -> cert -> index -> prop.
type decideR_je, storeR_jc,
     releaseL_je, releaseR_je      cert -> cert -> prop.
type initialL_je                   cert -> prop.
type initialR_je                   cert -> index -> prop.
type cut_je                        cert -> cert -> cert -> form -> prop.
type some_jc, all_jc               cert -> (i -> cert) -> prop.
type some_je, all_je               cert -> cert -> i -> prop.
type arr_jc, andPos_jc             cert -> cert -> prop.
type or_jc, andNeg_jc,
     arr_je, andPos_je             cert ->  cert -> cert -> prop.
type or_je, andNeg_je              cert -> cert -> choice -> prop.
type true_je                       cert -> prop.
type true_jc                       cert -> cert -> prop.
