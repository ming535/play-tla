------------------------------ MODULE traffic ------------------------------

NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"
                  
(*--algorithm traffic
variables
  at_light = TRUE,
  light = "red";
  
process light = "light"
begin
  Cycle:
    while at_light do
      light := NextColor(light);
    end while;
end process;
  
  
fair process car = "car"
begin
  Drive:
    when light = "green";
    at_light := FALSE;
end process;

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-1018a6757b5cbfb4258fd50888f1d5af
\* Process light at line 11 col 1 changed to light_
VARIABLES at_light, light, pc

vars == << at_light, light, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ light = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
                                        [] self = "car" -> "Drive"]

Cycle == /\ pc["light"] = "Cycle"
         /\ IF at_light
               THEN /\ light' = NextColor(light)
                    /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
               ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
                    /\ light' = light
         /\ UNCHANGED at_light

light_ == Cycle

Drive == /\ pc["car"] = "Drive"
         /\ light = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ light' = light

car == Drive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == light_ \/ car
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(car)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-e881586f427a2c9369bbfeb6132219a9

=============================================================================
\* Modification History
\* Last modified Fri Oct 30 20:31:41 CST 2020 by ming
\* Created Fri Oct 30 16:43:33 CST 2020 by ming
