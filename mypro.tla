------------------------------- MODULE mypro -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_queue

variable queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define; 


procedure add_to_queue(val="") begin
  Add:
    await Len(queue) < MaxQueueSize;
    queue := Append(queue, val);
    return;
end procedure;

process writer = "writer"
begin Write:
    while TRUE do
        call add_to_queue("msg");
    end while;
end process;

process reader \in {"r1", "r2"}
variables current_message = "none";
begin Read:
    while TRUE do
        await queue /= <<>>;
        current_message := Head(queue);
        queue := Tail(queue);
        either
          skip;
        or
          NotifyFailure:
            current_message := "none";
            call add_to_queue(self);
        end either;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-3caeaf4ddfefae518b89a53c90ebd6da
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
                 \/ /\ pc' = [pc EXCEPT ![self] = "NotifyFailure"]
              /\ UNCHANGED << stack, val >>

NotifyFailure(self) == /\ pc[self] = "NotifyFailure"
                       /\ current_message' = [current_message EXCEPT ![self] = "none"]
                       /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "add_to_queue",
                                                                   pc        |->  "Read",
                                                                   val       |->  val[self] ] >>
                                                               \o stack[self]]
                          /\ val' = [val EXCEPT ![self] = self]
                       /\ pc' = [pc EXCEPT ![self] = "Add"]
                       /\ queue' = queue

reader(self) == Read(self) \/ NotifyFailure(self)

Next == writer
           \/ (\E self \in ProcSet: add_to_queue(self))
           \/ (\E self \in {"r1", "r2"}: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-6bc053c6697c17eb39c3584c7181aa0f

=============================================================================
\* Modification History
\* Last modified Thu Oct 29 16:56:34 CST 2020 by ming
\* Created Thu Oct 29 15:55:27 CST 2020 by ming
