-------------------------------- MODULE VSR --------------------------------

(*  VIEWSTAMPED REPLICATION TLA+ SPECIFICATION
Based on Viewstamped Replication Revisited
https://pmg.csail.mit.edu/papers/vr-revisited.pdf

Author: Jack Vanlightly

WORK-IN-PROGRESS

So far:
- No normal operations (coming next)
- View changes, but no client table.
    - Use InitWithData to setup a scenario for now (until normal ops added)
    - Basic safety and liveness
        - Safety: no replica in normal state can have a commit number
                  lower than the highest acknowledged op.
        - Liveness: View changes eventually complete.
- No recovery
- No reconfiguration
- No explicit failures
    - Messages may never be received, so the unavailability of
      a minority is kind handled anyway. However, with
      weak fairness of Next, it doesn't explore unavailability
      of a majority.

Accronyms used:
- SVC = StartViewChange
- DVC = DoViewChange
- SV  = StartView

Current questions:
1) The view change description in the paper seems to conflict
   with itself. What are the conditions for a replica to change 
   its view number? My interpretation:
        a) when the timer expires, the replica sets v to v+1
        b) when receiving a SVC with higher v. Replica sets v to match message.
        c) when receiving a DVC with higher v. Replica sets v to match message.
        d) When receiving a SV with higher v. Replica sets v to match message.
        d) When SVC, DVC or SV of the same view number, replica makes no change.
        e) SVC, DVC or SV of lower view number are ignored.
   However, in the paper it says:
   "When the new primary receives f + 1
    DOVIEWCHANGE messages from different
    replicas (including itself), it sets its view-number
    to that in the messages."
   This doesn't match my rules (a)-(e), but I can't see what rules
   would make this sentence in the paper valid. 
2) The paper does not explain what should happen if a replica 
   receives an SVC message of view X after having
   received an SV message of the same view X. It could:
   a) register the message and switch back to ViewChange status.
   b) register the SVC message but remain in Normal status.
   c) ignore the message.
   Choosing (a) would cause unavailability if it were the primary,
   so the only good choices are (b) and (c). This specification
   uses option (c).

*)

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, TLCExt

\* Model size
CONSTANTS ReplicaCount,
          ClientCount,
          StartViewOnTimerLimit

\* Status          
CONSTANTS Normal,
          ViewChange,
          Recovering

\* Message types          
CONSTANTS RequestMsg,
          PrepareMsg,
          PrepareOkMsg,
          CommitMsg,
          StartViewChangeMsg,
          DoViewChangeMsg,
          StartViewMsg,
          RecoveryMsg,
          RecoveryResponseMsg
                              
CONSTANTS Nil

VARIABLES replicas,                 \* set of replicas as integers
          rep_status,               \* function of replica -> status
          rep_log,                  \* function of replica -> log
          rep_view_number,          \* function of replica -> view number
          rep_op_number,            \* function of replica -> op number
          rep_commit_number,        \* function of replica -> commit number
          rep_client_table,         \* function of replica -> client table
          rep_last_normal_view,     \* function of replica -> last normal view
          rep_svc_recv,             \* function of replica -> set of SVC msgs received
          rep_dvc_recv,             \* function of replica -> set of DVC msgs received
          rep_sent_dvc,             \* function of replica -> TRUE/FALSE whether DVC was sent
          rep_sent_sv,              \* function of replica -> TRUE/FALSE whether SV was sent
          clients,
          client_req_number,
          messages,                 \* messages as a function of message -> pending deliveries
          aux_svc,                  \* used to track number of times a timer-based SVC is sent
          aux_client_acked          \* used to track which operations have been acknowledged

rep_state_vars == << rep_status, rep_log, rep_view_number, rep_op_number,
                     rep_commit_number, rep_client_table, rep_last_normal_view >>
rep_vc_vars == << rep_svc_recv, rep_dvc_recv, rep_sent_dvc, rep_sent_sv >>
client_vars    == << client_req_number >>
aux_vars       == << aux_svc, aux_client_acked >>             
vars           == << rep_state_vars, rep_vc_vars, client_vars, aux_vars, 
                     replicas, clients, messages >> 
          
\*****************************************
\* Message passing
\*****************************************

\* Send the message whether it already exists or not.
SendFunc(m, msgs) ==
    IF m \in DOMAIN msgs
    THEN [msgs EXCEPT ![m] = @ + 1]
    ELSE msgs @@ (m :> 1)

BroadcastFunc(msg, source, msgs) ==
    LET bcast_msgs == { [msg EXCEPT !.dest = r] 
                    : r \in replicas \ {source} }
        new_msgs   == bcast_msgs \ DOMAIN msgs
    IN [m \in DOMAIN msgs |->
            IF m \in bcast_msgs
            THEN msgs[m] + 1
            ELSE msgs[m]] @@ [r \in new_msgs |-> 1]    

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardFunc(m, msgs) ==
    [msgs EXCEPT ![m] = @ - 1]

Send(m) ==
    messages' = SendFunc(m, messages)

Discard(d) ==
    messages' = DiscardFunc(d, messages)
    
Broadcast(msg, source) ==
    messages' = BroadcastFunc(msg, source, messages) 

DiscardAndBroadcast(d, msg, source) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = BroadcastFunc(msg, 
                     source,
                     DiscardFunc(d, messages))
    
DiscardAndSend(d, m) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = SendFunc(m, DiscardFunc(d, messages))

ReceivableMsg(m, type, r) ==
    /\ m.type = type
    /\ m.dest = r
    /\ messages[m] > 0

\*****************************************
\* Helpers
\*****************************************

View(r) ==
    rep_view_number[r]

\* v=1, rc=3 => p=1
\* v=2, rc=3 => p=2
\* v=3, rc=3 => p=3
Primary(v) ==
    1 + ((v-1) % ReplicaCount)

NewSVCMessage(r, view_number) ==
    [type        |-> StartViewChangeMsg,
     view_number |-> view_number,
     dest        |-> Nil, \* replaced in broadcast
     source      |-> r]

ResetSentVars(r) ==
    /\ rep_sent_dvc' = [rep_sent_dvc EXCEPT ![r] = FALSE]
    /\ rep_sent_sv' = [rep_sent_sv EXCEPT ![r] = FALSE]
    
    
\*****************************************
\* Actions
\*****************************************

\*****************************************
\* Init
\* Starts off with an established cluster with no data

Init ==
    LET replica_ids == 1..ReplicaCount
        client_ids == 1..ClientCount
    IN 
        /\ replicas = replica_ids
        /\ rep_status = [r \in replica_ids |-> Normal]
        /\ rep_log = [r \in replica_ids |-> <<>>]
        /\ rep_view_number = [r \in replica_ids |-> 0]
        /\ rep_op_number = [r \in replica_ids |-> 0]
        /\ rep_commit_number = [r \in replica_ids |-> 0]
        /\ rep_client_table = [r \in replica_ids |-> 
                                [c \in client_ids |-> Nil]]
        /\ rep_svc_recv = [r \in replica_ids |-> {}]
        /\ rep_dvc_recv = [r \in replica_ids |-> {}]
        /\ rep_sent_dvc = [r \in replica_ids |-> FALSE]
        /\ rep_sent_sv = [r \in replica_ids |-> FALSE]
        /\ rep_last_normal_view = [r \in replica_ids |-> 0]
        /\ clients = client_ids
        /\ client_req_number = [c \in client_ids |-> 0]
        /\ messages = <<>>
        /\ aux_svc = 0
        /\ aux_client_acked = <<>>
        
\* set up initial state with some data to test stuff out
\* until normal operations implemented      
InitWithData ==
    LET replica_ids == 1..ReplicaCount
        client_ids == 1..ClientCount
        reps_with_data == {1,2} \* set to {1} to see invariant violation
    IN 
        /\ replicas = replica_ids
        /\ rep_status = [r \in replica_ids |-> Normal]
        /\ rep_log = [r \in replica_ids |-> 
                        IF r \in reps_with_data
                        THEN << [op_number |-> 1] >>
                        ELSE <<>>]
        /\ rep_view_number = [r \in replica_ids |-> 
                        IF r \in reps_with_data THEN 2 ELSE 1]
        /\ rep_op_number = [r \in replica_ids |-> 
                        IF r \in reps_with_data THEN 1 ELSE 0]
        /\ rep_commit_number = [r \in replica_ids |-> 
                        IF r \in reps_with_data THEN 1 ELSE 0]
        /\ rep_client_table = [r \in replica_ids |-> 
                                [c \in client_ids |-> Nil]]
        /\ rep_svc_recv = [r \in replica_ids |-> {}]
        /\ rep_dvc_recv = [r \in replica_ids |-> {}]
        /\ rep_sent_dvc = [r \in replica_ids |-> FALSE]
        /\ rep_sent_sv = [r \in replica_ids |-> FALSE]
        /\ rep_last_normal_view = [r \in replica_ids |-> 
                         IF r \in reps_with_data THEN 2 ELSE 1]
        /\ clients = client_ids
        /\ client_req_number = [c \in client_ids |-> 0]
        /\ messages = <<>>
        /\ aux_svc = 0
        /\ aux_client_acked = (1 :> TRUE)

\*****************************************
\* TimerSendSVC
\* 
\* StartViewChange on a timer. The replica hasn't 
\* heard from the primary. Broadcasts a SVC message to 
\* all other replicas.
\* Resets recorded (received SVCs and DVCs, sent DVCs and SVs).

TimerSendSVC ==
    /\ aux_svc < StartViewOnTimerLimit
    /\ \E r \in replicas :
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = View(r) + 1]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = {}]
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = {}]
        /\ ResetSentVars(r)
        /\ aux_svc' = aux_svc + 1
        /\ Broadcast(NewSVCMessage(r, View(r) + 1), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_client_table, 
                        rep_last_normal_view, client_vars, replicas, clients, aux_client_acked >>
                      
\*****************************************
\* ReceiveHigherSVC (StartViewChange)
\*
\* A replica receives a StartViewChange message
\* with a higher view number than it's own. The
\* replica updates it view to match and broadcasts
\* a StartViewChange of its own.
\* Resets recorded (received SVCs and DVCs, sent DVCs and SVs)
\* but records the SVC received. 

ReceiveHigherSVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, StartViewChangeMsg, r)
        /\ m.view_number > rep_view_number[r]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = {m}]
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = {}]
        /\ ResetSentVars(r)
        /\ DiscardAndBroadcast(m, NewSVCMessage(r, m.view_number), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_client_table, 
                        rep_last_normal_view, client_vars, aux_vars, replicas, clients >>

\*****************************************
\* ReceiveMatchingSVC (StartViewChange)
\*
\* A replica receives a StartViewChange message
\* with a view number that matches it's own. In this
\* action it simply records the message.
\* NOTE: seems obvious that we shouldn't let a replica
\*       in a switch from normal->view-change status
\*       without a view number change, this could cause 
\*       a liveness issue. Not discussed in the paper.
ReceiveMatchingSVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, StartViewChangeMsg, r)
        /\ m.view_number = View(r)
        \* prevent switching to ViewChange without a view number change (not in paper)
        /\ rep_status[r] = ViewChange 
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = @ \union {m}]
        /\ Discard(m)
        /\ UNCHANGED << rep_state_vars, rep_dvc_recv, rep_sent_dvc, rep_sent_sv,
                        client_vars, aux_vars, replicas, clients >>

\*****************************************
\* SendDVC (DoViewChange)
\* The replica has received StartViewChange messages
\* from a minority (f) replicas and therefore sends
\* a DoViewChange to the primary of this view.
\* It includes:
\* - the highest view number that was in a normal status
\* - it's log (this will be replaced by optimizations later on)
\* - the view number, op number and commit number.
\* If the primary is itself, it doesn't send the message, it
\* only registers it for counting.

SendDVC ==
    \E r \in replicas :
        /\ rep_sent_dvc[r] = FALSE
        /\ Cardinality(rep_svc_recv[r]) >= ReplicaCount \div 2
        /\ rep_sent_dvc' = [rep_sent_dvc EXCEPT ![r] = TRUE]
        /\ LET msg == [type           |-> DoViewChangeMsg,
                       view_number    |-> View(r),
                       log            |-> rep_log[r],
                       last_normal_vn |-> rep_last_normal_view[r],
                       op_number      |-> rep_op_number[r],
                       commit_number  |-> rep_commit_number[r],
                       dest           |-> Primary(View(r)),
                       source         |-> r]
           IN \/ /\ Primary(View(r)) = r
                 /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = @ \union {msg}]
                 /\ UNCHANGED messages
              \/ /\ Primary(View(r)) # r
                 /\ Send(msg)
                 /\ UNCHANGED rep_dvc_recv
        /\ UNCHANGED << rep_state_vars, rep_svc_recv, rep_sent_sv, 
                        client_vars, aux_vars, replicas, clients >>
            
\*****************************************
\* ReceiveHigherDVC (DoViewChange)
\*
\* A replica receives a DoViewChange with a higher view
\* than its own. The replica updates it view to match 
\* and broadcasts a StartViewChange of its own. 
ReceiveHigherDVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, DoViewChangeMsg, r)
        /\ m.view_number > rep_view_number[r]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = {}]
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = {m}]
        /\ ResetSentVars(r)
        /\ DiscardAndBroadcast(m, NewSVCMessage(r, m.view_number), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_client_table, 
                        rep_last_normal_view, aux_vars, client_vars, replicas, clients >>
            
\*****************************************
\* ReceiveMatchingDVC (DoViewChange)
\*
\* A replica receives a DoViewChange that matches its
\* own view. It only registers the message for counting.

ReceiveMatchingDVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, DoViewChangeMsg, r)
        /\ View(r) = m.view_number
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = @ \union {m}]
        /\ Discard(m)
        /\ UNCHANGED << rep_state_vars, rep_svc_recv, rep_sent_dvc, rep_sent_sv,
                        client_vars, aux_vars, replicas, clients >>

\*****************************************
\* SendSV (StartView)
\*
\* A replica has received DoViewChange messages from
\* a majority (including itself) and so it assumes
\* leadership by broadcasting a StartView message to
\* all other replicas. It includes:
\* - the log (this will be replaced by optimizations later on)
\* - the op and commit numbers
\* - sets some vars for accounting purposes

HighestLog(r) ==
    LET m == CHOOSE m \in rep_dvc_recv[r] :
                ~\E m1 \in rep_dvc_recv[r] :
                    \/ m1.last_normal_vn > m.last_normal_vn
                    \/ /\ m1.last_normal_vn = m.last_normal_vn
                       /\ m1.op_number > m.op_number
    IN m.log

HighestOpNumber(r) ==
    IF HighestLog(r) = <<>>
    THEN 0
    ELSE Last(HighestLog(r)).op_number

HighestCommitNumber(r) ==
    LET m == CHOOSE m \in rep_dvc_recv[r] :
                ~\E m1 \in rep_dvc_recv[r] :
                    \/ m1.commit_number > m.commit_number
    IN m.commit_number
        
SendSV ==
    \E r \in replicas :
        /\ rep_sent_sv[r] = FALSE
        /\ Cardinality(rep_dvc_recv[r]) >= (ReplicaCount \div 2) + 1
        /\ LET new_log == HighestLog(r)
               new_on  == HighestOpNumber(r)
               new_cn  == HighestCommitNumber(r)
           IN
                /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
                /\ rep_view_number' = [rep_view_number EXCEPT ![r] = View(r)]
                /\ rep_log' = [rep_log EXCEPT ![r] = new_log]
                /\ rep_op_number' = [rep_op_number EXCEPT ![r] = new_on]
                /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = new_cn]
                /\ rep_sent_sv' = [rep_sent_sv EXCEPT ![r] = TRUE]
                /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = View(r)]
                /\ Broadcast([type          |-> StartViewMsg,
                              view_number   |-> View(r),
                              log           |-> new_log,
                              op_number     |-> new_on,
                              commit_number |-> new_cn,
                              dest          |-> Nil,
                              source        |-> r], r)
        /\ UNCHANGED << rep_client_table, rep_svc_recv, rep_dvc_recv, rep_sent_dvc, 
                        client_vars, aux_vars, replicas, clients >>

\*****************************************
\* ReceiveSV (StartView)
\* A replica receives a StartView message and updates
\* its state accordingly. If the replica has any
\* uncommitted operations in its log, it sends the
\* primary a PrepareOk message with the op number
\* it rceived from the primary.
\* NOTE: There is no restriction about view numbers here,
\*       a replica can switch to an earlier view. Most
\*       likely an omission of the paper.

ReceiveSV ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, StartViewMsg, r)
        /\ m.view_number >= View(r)
        /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_log' = [rep_log EXCEPT ![r] = m.log]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = m.commit_number]
        /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = m.view_number]
        /\ IF rep_commit_number[r] < m.op_number
           THEN DiscardAndSend(m, [type      |-> PrepareOkMsg,
                                   op_number |-> m.op_number,
                                   dest      |-> Primary(m.view_number),
                                   source    |-> r])
           ELSE Discard(m)
        /\ UNCHANGED << rep_client_table, rep_vc_vars, 
                        client_vars, aux_vars, replicas, clients >>
                  
       
Next ==
    \* view changes
    \/ TimerSendSVC
    \/ ReceiveHigherSVC
    \/ ReceiveMatchingSVC
    \/ SendDVC
    \/ ReceiveHigherDVC
    \/ ReceiveMatchingDVC
    \/ SendSV
    \/ ReceiveSV
    \* normal operations
    \* TODO
    \* recovery
    \* TODO
    \* reconfiguration
    \* TODO

\*****************************************
\* Invariants
\*****************************************

NoAcknowledgedWritesBelowCommitNumber ==
    ~\E op \in DOMAIN aux_client_acked :
        /\ aux_client_acked[op] = TRUE
        /\ \E r \in replicas :
            /\ rep_status[r] = Normal
            /\ rep_commit_number[r] < op

TestInv == TRUE

\*****************************************
\* Liveness
\*****************************************

AllReplicasMoveToSameView ==
    \A r1, r2 \in replicas :
        /\ rep_view_number[r1] = rep_view_number[r2]
        /\ rep_status[r1] = Normal
        /\ rep_status[r2] = Normal

ViewChangeCompletes ==
    []<>AllReplicasMoveToSameView
    
  
  
    
Spec == InitWithData /\ [][Next]_vars /\ WF_vars(Next)    

=============================================================================
