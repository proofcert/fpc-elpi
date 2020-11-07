sig ljf-certificates.
accum_sig ljf-formulas.

kind cert, index                         type.
kind choice                              type.
type left, right                       choice.

type storeC                     cert -> cert -> index -> o.
type decideE                    cert -> cert -> index -> o.
type decideR_je, storeR_jc,
     releaseL_je, releaseR_je      cert -> cert -> o.
type initialE                   cert -> o.
type initialR_je                   cert -> index -> o.
type cut_je                        cert -> cert -> cert -> form -> o.
type some_jc, all_jc               cert -> (i -> cert) -> o.
type some_je, all_je               cert -> cert -> i -> o.
type impC, andPos_jc             cert -> cert -> o.
type or_jc, andNeg_jc,
     impE, andPos_je             cert ->  cert -> cert -> o.
type or_je, andNeg_je              cert -> cert -> choice -> o.
type true_je                       cert -> o.
type true_jc                       cert -> cert -> o.
