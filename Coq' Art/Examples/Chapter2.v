Require Import Arith.
Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Locate "_ * _".
Print Scope Z_scope.

Check 33%nat.
Check 33.


Check 0.
Open Scope nat_scope.
Check 0.

Check orb.
Print orb.

Check (S(S(S O))).
Check (S(S(S 0))).

Check (mult (mult 5 (minus 5 4)) 7).
Check (5*(5-4)*7).

Set Printing All.
Check 4.
Check (5*(5-4)*7).
Unset Printing All.

Close Scope nat_scope.
Close Scope Z_scope.


Open Scope nat_scope.
Open Scope Z_scope.
Check (fun n (z:Z) f => (n+((f z)))%nat).

Check fun n p : nat => (
    let diff := n-p in
    let square := diff*diff in
    square * (square+n)
)%nat.

Parameter max_int : Z.

Section binomial_def.
    Variables a b : Z.
    Definition binomial z:Z := a*z + b.
    Section trinomial_def.
        Variables c : Z.
        Definition trinomial z:Z := (binomial z)*z + c.
    End trinomial_def.
End binomial_def.

Definition zsqr (z:Z) : Z := z*z.
Definition Zappl (f:Z->Z)(z:Z) : Z := f (f z).
Check zsqr.
Check Zappl.

Eval cbv delta [Zappl zsqr] in (Zappl zsqr).
Eval cbv beta delta [Zappl zsqr] in (Zappl zsqr).
Eval cbv beta zeta delta [Zappl zsqr] in (Zappl zsqr).
Eval cbv iota beta zeta delta [Zappl zsqr] in (Zappl zsqr).
Eval compute [Zappl zsqr] in (Zappl zsqr).



Check Z.
Check Set.
Check Type.

Section realization.
    Variables (A B :Set).
    Let spec : Set := (((A -> B) ->B)->B)->A->B.

Let realization : spec :=
    fun (f:((A -> B)->B)->B) a => f (fun g => g a).
