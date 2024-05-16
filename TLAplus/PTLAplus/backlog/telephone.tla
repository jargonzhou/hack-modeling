----------------------------- MODULE telephone -----------------------------
EXTENDS Sequences, TLC

(*--algorithm telephone
variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {},
    can_send = TRUE;

\* WARN: Deadlock reached.
\* sender depend on reciver to set can_send.

begin
    while Len(received) /= 3 do
        \* send
        if can_send /\ to_send /= <<>> then
            in_transit := in_transit \union {Head(to_send)};
            can_send := FALSE;
            to_send := Tail(to_send);
        end if;
        
        \* receive
        either
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
                \* case: the message is successfully received,
                \*       but the mechanism that reports it was received fails.
                either
                    can_send := TRUE;
                or
                    skip;
                end either;
            end with;
        or
            skip;
        end either;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "efca550a" /\ chksum(tla) = "347d63ea")
VARIABLES to_send, received, in_transit, can_send, pc

vars == << to_send, received, in_transit, can_send, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ can_send = TRUE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF can_send /\ to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ can_send' = FALSE
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit, can_send >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit, can_send >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
              /\ \/ /\ can_send' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED can_send
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Thu Aug 18 11:52:20 CST 2022 by zhoujiagen
\* Created Thu Aug 18 10:35:45 CST 2022 by zhoujiagen
