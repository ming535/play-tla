------------------------------ MODULE recycler ------------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

(*--algorithm recycle

variables     
    capacity \in [trash: 1..10, recycle: 1..10], \* a set of structures 
    bins = [trash |-> {}, recycle |-> {}],
    count = [trash |-> 0, recycle |-> 0],
    item = [type: {"trash", "recycle"}, size: 1..6]
    items \in item \X item \X item \X item,
    curr = ""; \* helper: current item
    
macro add_item(type) begin
    bins[type] := bins[type] \union {curr};
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;
end macro;

begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycle" /\ curr.size < capacity.recycle then
            add_item("recycle");
        elsif curr.size < capacity.trash then
            add_item("trash");
        end if;
    end while;
    
    assert capacity.trash >=0 /\ capacity.recycle >= 0;
    assert Cardinality(bins.trash) =  count.trash;
    assert Cardinality(bins.recycle) = count.recycle; 
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7fa1390da8eb20c2dfcc47af40b97e08
VARIABLES capacity, bins, count, items, curr, pc

vars == << capacity, bins, count, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycle: 1..10]
        /\ bins = [trash |-> {}, recycle |-> {}]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ items =         [type: {"trash", "recycle"}, size: 1..6]
                   items \in item \X item \X item \X item
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle" /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = bins["recycle"] \union {curr'}]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = bins["trash"] \union {curr'}]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(capacity.trash >=0 /\ capacity.recycle >= 0, 
                              "Failure of assertion at line 31, column 5.")
                    /\ Assert(Cardinality(bins.trash) =  count.trash, 
                              "Failure of assertion at line 32, column 5.")
                    /\ Assert(Cardinality(bins.recycle) = count.recycle, 
                              "Failure of assertion at line 33, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2ef5fd09ad768194c3ff87d585522f7e

=============================================================================
\* Modification History
\* Last modified Fri Oct 23 10:57:11 CST 2020 by ming
\* Created Fri Oct 23 09:27:00 CST 2020 by ming
