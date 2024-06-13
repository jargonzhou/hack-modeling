---- MODULE message_queue ----
EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(**--algorithm alg
variable queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;

\* macro add_to_queue(val) begin
\*     await Len(queue) < MaxQueueSize; \* make sure queue is not full
\*     queue := Append(queue, val);
\* end macro;

procedure add_to_queue(val="") begin
    Add:
        await Len(queue) < MaxQueueSize;
        queue := Append(queue, val);
        return;
end procedure;

process writer = "writer"
begin Write:
    while TRUE do
        \* add_to_queue("msg") \* macro
        call add_to_queue("msg") \* procedure
    end while;
end process;

\* process reader = "reader"
process reader \in {"r1", "r2"} \* process sets
variables current_message = "none";
begin Read:
    while TRUE do
        await queue /= <<>>; \* make sure queue is not empty
        current_message := Head(queue);
        queue := Tail(queue);
        \* the possibly pattern
        either
            skip
        or
            NitifyFailure:
                current_message := "none";
                \* add_to_queue("fail") \* macro
                \* add_to_queue(self) 
                call add_to_queue(self) \* procedure
        end either;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "727afb60" /\ chksum(tla) = "e4839351")
VARIABLES queue, pc, stack

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLES val, current_message

vars == << queue, pc, stack, val, current_message >>

ProcSet == {"writer"} \cup ({"r1", "r2"})

Init == (* Global variables *)
        /\ queue = <<>>
        (* Procedure add_to_queue *)
        /\ val = [ self \in ProcSet |-> ""]
        (* Process reader *)
        /\ current_message = [self \in {"r1", "r2"} |-> "none"]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self \in {"r1", "r2"} -> "Read"]

Add(self) == /\ pc[self] = "Add"
             /\ Len(queue) < MaxQueueSize
             /\ queue' = Append(queue, val[self])
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED current_message

add_to_queue(self) == Add(self)

Write == /\ pc["writer"] = "Write"
         /\ /\ stack' = [stack EXCEPT !["writer"] = << [ procedure |->  "add_to_queue",
                                                         pc        |->  "Write",
                                                         val       |->  val["writer"] ] >>
                                                     \o stack["writer"]]
            /\ val' = [val EXCEPT !["writer"] = "msg"]
         /\ pc' = [pc EXCEPT !["writer"] = "Add"]
         /\ UNCHANGED << queue, current_message >>

writer == Write

Read(self) == /\ pc[self] = "Read"
              /\ queue /= <<>>
              /\ current_message' = [current_message EXCEPT ![self] = Head(queue)]
              /\ queue' = Tail(queue)
              /\ \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Read"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "NitifyFailure"]
              /\ UNCHANGED << stack, val >>

NitifyFailure(self) == /\ pc[self] = "NitifyFailure"
                       /\ current_message' = [current_message EXCEPT ![self] = "none"]
                       /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "add_to_queue",
                                                                   pc        |->  "Read",
                                                                   val       |->  val[self] ] >>
                                                               \o stack[self]]
                          /\ val' = [val EXCEPT ![self] = self]
                       /\ pc' = [pc EXCEPT ![self] = "Add"]
                       /\ queue' = queue

reader(self) == Read(self) \/ NitifyFailure(self)

Next == writer
           \/ (\E self \in ProcSet: add_to_queue(self))
           \/ (\E self \in {"r1", "r2"}: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
