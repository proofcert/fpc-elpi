module pnnf.

nnf (limp A B) (land NA (not NB)) :-
    nnf A NA, nnf B NB.

nnf (land  A B) (lor (not NA) (not NB)) :-
    nnf A NA, nnf B NB.

nnf (lor  A B) (land (not NA) (not NB)) :-
    nnf A NA, nnf B NB.

nnf (not (not A)) NA :-
    nnf A NA.

nnf(not (land A B)) (lor (not NA) (not NB)) :-
    nnf A NA, nnf B NB.

nnf(not (lor A B)) (land (not NA) (not NB)) :-
    nnf A NA, nnf B NB.

    
nnf (not (at A)) (not (at A)).
nnf (at A) (at A).
