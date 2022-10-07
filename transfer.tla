---- MODULE transfer ----
EXTENDS Integers, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in -10..20;
define
    MoneyNotNegative == money >= 0
end define;
begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;
C: assert alice_account >= 0;
end algorithm *)

\* BEGIN TRANSLATION (chksum(pcal) = "a18774f6" /\ chksum(tla) = "a7ed16b7")
VARIABLES alice_account, bob_account, money, pc

(* define statement *)
MoneyNotNegative == money >= 0


vars == << alice_account, bob_account, money, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in -10..20
        /\ pc = "A"

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << alice_account, money >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 12, column 4.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
