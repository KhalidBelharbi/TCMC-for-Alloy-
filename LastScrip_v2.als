   
	 abstract sig Transition {src: one State,dst:one State}
	// 	We add Completed_and_Cancel to represent the simultaneous presence of events Cancel_L_I and Completed_L_I 
    sig Completed_and_Cancel, Share,Completed_L_S,Restard,Completed_L_I,Completed_L_F,PeersDone,Start,Cancel_L_I,Cancel_S_I extends Transition {}
	{
// scenario 11 12
	(#Completed_and_Cancel =0 and #Share = 0 and #Completed_L_S = 1 and (#Restard = 0 or #Restard = 1) and #Completed_L_I = 0 and
	 #Completed_L_F = 0 and #Finishing = 0 and #PeersDone = 0 and #Start = 1 and #Cancel_L_I = 1 and #Cancel_S_I = 1) or 
// scenario 21 22
	(#Cancel_L_I = 0 and #Completed_L_I =0 and #Completed_and_Cancel =1 and  #Share = 1 and #Completed_L_S= 0 and (#Restard = 0 or #Restard = 1) and 
	#Completed_L_F = 0 and #Finishing = 0 and #PeersDone = 0 and #Start = 1 and #Cancel_S_I = 1) or
// scenario 31 32
	(#Completed_and_Cancel =0 and #Share = 1 and #Completed_L_S = 0 and (#Restard = 0 or #Restard = 1) and #Completed_L_I = 0 and #Completed_L_F = 1 and 
	#Finishing = 1 and #PeersDone = 1 and #Start = 1 and #Cancel_L_I = 1 and #Cancel_S_I = 1)}
    abstract sig State {Event:  some  Transition}
    sig Idle, Leeching, Seeding, Finishing extends State{
    }{  #Idle = 1
        #Leeching = 1 
        #Seeding = 1
        #Finishing<=1 // F can be abscent in some scenarios
    }
    one sig TS{
    	 State0: some Idle, // initial states
    	 states: some State, // all states
    	 transitions : set Transition, // transitions of our system
    	 next:  states -> states, // next set 
    	 relations: transitions one-> one next // each transition has one next, and one next has one transition
    }{ transitions.relations = next // the coherence between next set and transitions.relations set
		  }
fact Coherences {
    all t:Transition | t in TS.transitions // C1
    all s:State | s in TS.states // C2
    all t:TS.transitions | one s:TS.states | t in s.Event // C3
    all s:TS.states,t:TS.transitions | t in s.Event iff (one s2:TS.states | t.src =s and t.dst =s2 and t-> s-> s2 in TS.relations) // C4
    all elem : TS.transitions | elem.src->elem.dst = elem.(TS.relations)//C5
}
pred FromTO[s1,src_,s2,dst_:TS.states, e:Transition ] { // from s1 : src_ to s2:dst_ + e 
 s1 in src_ and s2 in dst_ and e.src = s1 and e.dst=s2
 }

fact properties { // The structure of our Partial Model
    all s1,s2:TS.states | s1->s2 in TS.next iff(
        FromTO[s1,Idle,s2,Leeching,Start] or
        FromTO[s1,Idle,s2,Seeding,Share] or
        FromTO[s1,Leeching,s2,Idle,Completed_L_I] or 
        FromTO[s1,Leeching,s2,Idle,Cancel_L_I] or 
	     FromTO[s1,Leeching,s2,Idle,Completed_and_Cancel] or 
        FromTO[s1,Leeching,s2,Seeding,Completed_L_S] or
        FromTO[s1,Leeching,s2,Finishing,Completed_L_F] or
        FromTO[s1,Seeding,s2,Idle,Cancel_S_I] or
        FromTO[s1,Seeding,s2,Leeching,Restard] or
        FromTO[s1,Finishing,s2,Idle,PeersDone] 
    )
}
// ***************************************** TCMC ********************************
fun initialState: State {TS.State0}
private fun domainRes[R: State -> State, X: State]: State -> State{X <: R}
private fun id[X:State]: State->State{domainRes[iden,X]}
fun not_[phi: State]: State {State - phi}
fun and_[phi, si: State]: State {phi & si}
fun or_[phi, si: State]: State {phi + si}
fun imp_[phi, si: State]: State {not_[phi] + si}
fun ex[phi: State]: State {TS.next.phi}
fun ax[phi:State]:State {not_[ex[not_[phi]]]}
fun ef[phi: State]: State {(*(TS.next)).phi }
fun eg[phi: State]: State {let R= domainRes[TS.next,phi]|*R.((^R & id[State]).State)}
fun af[phi: State]: State {not_[eg[not_[phi]]]}
fun ag[phi: State]: State {not_[ef[not_[phi]]]}
fun eu[phi, si: State]: State {(*(domainRes[TS.next, phi])).si}
pred ctl_mc[phi: State]{TS.State0 in phi}
// ***************************************** CTL checking ************************
assert CTL_Formula{ // here you can write your CTL spec
	ctl_mc[ ag[{
   	s:TS.states | s in Idle implies Seeding in s.(TS.next) // this is the SC1
	}] ]
}
check CTL_Formula for  9 
// ***************************************** Properties to check ************************
pred HC1 {
#Completed_and_Cancel = 0 // HC1 constraint
}
run showExamples {} for 9
run HC1 {} for 9

