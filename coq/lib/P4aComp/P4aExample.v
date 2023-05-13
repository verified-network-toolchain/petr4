From Poulet4.P4cub.Syntax Require Import Syntax P4Field.
From Poulet4.Utils Require Import FinType P4Arith Envn.
Require Import Coq.ZArith.ZArith
        Coq.micromega.Lia
        Coq.Bool.Bool.
Import String.
Open Scope string_scope.
Import ListNotations.
From Poulet4.P4aComp Require Import P4aComp.

Definition params := [("hdr",
(PAOut
   (Typ.Struct false
               [Typ.Struct true [Typ.Bit 48; Typ.Bit 48; Typ.Bit 16];
Typ.Struct true [Typ.Bit 40; Typ.Bit 10]])));
("meta", (PAInOut (Typ.Struct false [])))
] : Typ.params.

Definition parser_accept := 
  (Top.Parser "MyParser" [] [] [] 
  ([
   ("hdr",
     (PAOut
      (Typ.Struct false
       ([ ((Typ.Struct true ([ (Typ.Bit 48); (Typ.Bit 48); (Typ.Bit 16) ])))
        ]))));
    ("meta", (PAInOut (Typ.Struct false [])))
   ])
  (Stm.Trans (Trns.Direct (Lbl.Name 1)))
  ([
   (Stm.Trans (Trns.Direct (Lbl.Name 1)));
    (Stm.Seq
     (Stm.App (Call.Method "packet_in" "extract" [] None)
      ([
       ((PAOut
         (Exp.Member (Typ.Bit 48) 0
          (Exp.Var
           (Typ.Struct false
            ([
             ((Typ.Struct true
               ([ (Typ.Bit 48); (Typ.Bit 48); (Typ.Bit 16) ])))
             ]))
           "hdr" 0))))
       ]))
     (Stm.Trans (Trns.Direct Lbl.Accept)))
   ])).

Definition test_extract := 
  (Stm.App (Call.Method "packet_in" "extract" [] (None))
      ([
       ((PAOut
         (Exp.Member (Typ.Bit 48) 0
          (Exp.Var
           (Typ.Struct false
            ([
             ((Typ.Struct true
               ([ (Typ.Bit 48); (Typ.Bit 48); (Typ.Bit 16) ])))
             ]))
           "hdr" 0))))
       ])).


Compute translate_st (find_hdrs parser_accept) test_extract.

Definition test_parser := 
  (Top.Parser "MyParser" [] ([]) [] params
  (Stm.Trans (Trns.Direct (Lbl.Name 1)))
  ([
   (Stm.Trans (Trns.Direct (Lbl.Name 1)));
    (Stm.Seq
     (Stm.App (Call.Method "packet_in" "extract" [] (None))
      ([
       ((PAOut
         (Exp.Member (Typ.Bit 48) 0
          (Exp.Var
           (Typ.Struct false
            ([
             ((Typ.Struct true
               ([ (Typ.Bit 48); (Typ.Bit 48); (Typ.Bit 16) ])))
             ]))
           "hdr" 0))))
       ]))
     (Stm.Trans
      (Trns.Select
       (Exp.Lists Lst.Struct
        ([
         ((Exp.Member (Typ.Bit 16) 2
           (Exp.Member (Typ.Bit 48) 0
            (Exp.Var
             (Typ.Struct false
              ([
               ((Typ.Struct true
                 ([ (Typ.Bit 48); (Typ.Bit 48); (Typ.Bit 16) ])))
               ]))
             "hdr" 0))))
         ]))
       Lbl.Accept ([ ((Pat.Lists ([ ((Pat.Bit 16 2049)) ])), Lbl.Start) ]))))
   ])).
