sig lkf-certificates.

kind cert, index                         type.
kind choice                              type.
type left, right                       choice.

type all_kc                  cert -> (A -> cert) -> o.
type andNeg_kc               cert -> cert -> cert -> o.
type andPos_ke               cert -> cert -> cert -> o.
type cut_ke                  cert -> cert -> cert -> form -> o.
type decide_ke               cert -> cert -> index -> o.
type false_kc                cert -> cert -> o.
type initial_ke              cert -> index -> o.
type orNeg_kc                cert -> cert -> o.
type orPos_ke                cert -> cert -> choice -> o.
type release_ke              cert -> cert -> o.
type some_ke                 cert -> cert -> A -> o.
type store_kc                cert -> (A -> cert) -> (A -> index) -> o.
type true_ke                 cert -> o.


