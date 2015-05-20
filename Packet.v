(** NetKAT Packets *)
Require Export Field Value Classes.

Module Type PACKET (F : FIELDSPEC) (V : VALUESPEC(F)).
  Definition t : Type := forall f:F.t, (V.t f).
  Parameter finite : Finite t.
  Parameter eq_dec : EqType t.
  Global Instance : Finite t := finite.
  Global Instance : EqType t := eq_dec.
  Parameter mod : t -> forall f : F.t, V.t f -> t.
End PACKET.



Module Packet (F : FIELDSPEC) (V : VALUESPEC(F)) : PACKET(F)(V).

  Definition t : Type := forall f:F.t, (V.t f).

  (* feel the power of automatic instance resolution...!! *)
  Definition finite : Finite t := _.
  Definition eq_dec : EqType t := dep_fun_EqType _ _.
  Global Instance : Finite t := finite.
  Global Instance : EqType t := eq_dec.

  Program Definition mod (pk : t) (f : F.t) (v : V.t f) : t :=
    fun f' => if (f' =d= f)%bool then v else pk f'.

End Packet.

