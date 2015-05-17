Require Export Field Value Packet Classes.

Module Type HISTORY (F : FIELDSPEC) (V : VALUESPEC(F)) (P : PACKET(F)(V)).
  Definition t : Type := (P.t * list P.t)%type.
  Parameter eq_dec : EqType t.
  Global Instance : EqType t := eq_dec.
End HISTORY.


Module History(F : FIELDSPEC) (V : VALUESPEC(F)) (P : PACKET(F)(V)) 
     : HISTORY(F)(V)(P).
  
  Definition t : Type := (P.t * list P.t)%type.

  (* feel the power of automatic instance resolution...!! *)
  Definition eq_dec : EqType t := _.
  Global Instance : EqType t := eq_dec.

End History.