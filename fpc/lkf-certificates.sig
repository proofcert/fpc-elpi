sig lkf-certificates.
accum_sig lkf-formulas.

kind cert, index                         type.
kind choice                              type.
type left, right                       choice.

type all_kc                  cert -> (A -> cert) -> prop.
type andNeg_kc               cert -> cert -> cert -> prop.
type andPos_ke               cert -> cert -> cert -> prop.
type cut_ke                  cert -> cert -> cert -> form -> prop.
type decide_ke               cert -> cert -> index -> prop.
type false_kc                cert -> cert -> prop.
type initial_ke              cert -> index -> prop.
type orNeg_kc                cert -> cert -> prop.
type orPos_ke                cert -> cert -> choice -> prop.
type release_ke              cert -> cert -> prop.
type some_ke                 cert -> cert -> A -> prop.
type store_kc                cert -> cert -> index -> prop.
type true_ke                 cert -> prop.


