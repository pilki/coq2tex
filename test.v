Fixpoint size_cont (k: cont) : nat :=
  match k with
  | Kseq s k1 => (size_stmt s + size_cont k1 + 1)
  | Kblock k1 => (size_cont k1 + 1)
  | _ => 0%nat
  end.

Definition measure_state (S: Cminor.Selstate) :=
  match S with
  | CminorSel.State _ s k _ _ _ =>
      existS (fun (x: nat) => nat)
             (size_stmt s + size_cont k)
             (size_stmt s)
  | _ =>
      existS (fun (x: nat) => nat) 0 0
  end.

Inductive bite :=
| bite.

