---- MODULE database ----
EXTENDS TLC, Integers, Sequences
CONSTANTS Data, NULL, Clients

(**--algorithm database
variables 
    query = [c \in Clients |-> NULL],
    ghost_db_history = [c \in Clients |-> NULL];

\* Definitions
define
    Exists(val) == val /= NULL
    RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;

\* Macro
macro request(data) begin
    query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
    await query[self].type = "response";
end macro;

\* Procedure
\* AlgorithmBody or Process
process clients \in Clients
variables result = NULL;
begin
    Reqeust:
        while TRUE do
            either \* read
                request([request |-> "read"]);
                Confirm:
                    wait_for_response();
                    result := query[self].result;
                    assert result = ghost_db_history[self];
            or \* write
                with d \in Data do
                    request([request |-> "write", data |-> d]);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while;
end process;

process database = "Database"
variable db_value \in Data;
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            if q.request = "write" then
                db_value := q.data;
            elsif q.request = "read" then
                skip;
            else 
                assert FALSE;
            end if;
            ghost_db_history[client] := db_value;
            query[client] := [type |-> "response", result |-> db_value];
        end with;
    
    goto DB;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cf222ff7" /\ chksum(tla) = "fd203aea")
VARIABLES query, ghost_db_history, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}

VARIABLES result, db_value

vars == << query, ghost_db_history, pc, result, db_value >>

ProcSet == (Clients) \cup {"Database"}

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
        /\ ghost_db_history = [c \in Clients |-> NULL]
        (* Process clients *)
        /\ result = [self \in Clients |-> NULL]
        (* Process database *)
        /\ db_value \in Data
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Reqeust"
                                        [] self = "Database" -> "DB"]

Reqeust(self) == /\ pc[self] = "Reqeust"
                 /\ \/ /\ query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "read"])]
                       /\ pc' = [pc EXCEPT ![self] = "Confirm"]
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([request |-> "write", data |-> d])]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                 /\ UNCHANGED << ghost_db_history, result, db_value >>

Confirm(self) == /\ pc[self] = "Confirm"
                 /\ query[self].type = "response"
                 /\ result' = [result EXCEPT ![self] = query[self].result]
                 /\ Assert(result'[self] = ghost_db_history[self], 
                           "Failure of assertion at line 37, column 21.")
                 /\ pc' = [pc EXCEPT ![self] = "Reqeust"]
                 /\ UNCHANGED << query, ghost_db_history, db_value >>

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Reqeust"]
              /\ UNCHANGED << query, ghost_db_history, result, db_value >>

clients(self) == Reqeust(self) \/ Confirm(self) \/ Wait(self)

DB == /\ pc["Database"] = "DB"
      /\ \E client \in RequestingClients:
           LET q == query[client] IN
             /\ IF q.request = "write"
                   THEN /\ db_value' = q.data
                   ELSE /\ IF q.request = "read"
                              THEN /\ TRUE
                              ELSE /\ Assert(FALSE, 
                                             "Failure of assertion at line 58, column 17.")
                        /\ UNCHANGED db_value
             /\ ghost_db_history' = [ghost_db_history EXCEPT ![client] = db_value']
             /\ query' = [query EXCEPT ![client] = [type |-> "response", result |-> db_value']]
      /\ pc' = [pc EXCEPT !["Database"] = "DB"]
      /\ UNCHANGED result

database == DB

Next == database
           \/ (\E self \in Clients: clients(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
====
