From elpi Require Import elpi.
Require Import dep_pbt.
Load deplist.

Goal forall (n: nat) (l: ilist nat n), rev l = l.
intros.
elpi dep_pbt 5 (True) (l).
Abort.

Goal exists n, hd (repeat 5 5) = n. 
intros. Fail elpi dep_pbt 5.