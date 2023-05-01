#lang forge
-- Import all the elevator procedures to critique, along with
--   all of the sigs and predicates:
open "elevator.frg"


/*------------------------------------*\
|    Elevator Procedure Descriptions   |
\*------------------------------------*/

-- Procedure 1:
// Procedure 1 states the elevator will always move in the direction where a request occurs. Explicitly, 
// the elevator will stay still if and only if there are no requests and it always picks up the current floor 
// if there is a request on that floor. The elevator will not go up if there are requests below it and it will 
// not go down if there are no requests below it: defining the movement that the elevator will move to where a single 
// request arises.

-- Procedure 2:
// This procedure ensures that the elevator is constantly moving (no stagnant states) between the bottom and top floors. 
// It defines behavior if the elevator is left at the top or the bottom floors (if at bottom, move to top and vice-versa). 
// It has no regard for the requests other than if the current floor is requesting, and defines behavior to ensure the 
// elevator never stays still. 

-- Procedure 3:
// Procedure 3 defines behavior for the elevator depending on where the request is. If there is a request above the current floor, 
// then the elevator will move up, and vice-versa for movement down on requests below the floor. If there are no requests, 
// then the elevator stays still. It should always pick up the current floor if there is a request, however. This procedure may become 
// problematic if multiple requests arise.

-- Procedure 4:
// Procedure 4 revolves around moving to different requests as needed, and handles nextRequest updates from state-to-state. 
// It picks up the current floor if there is a request, moves up if the next request is above the current floor, moves down 
// if the next request is below the current floor, and handles cases when the elevator starts on the bottom with no requests 
// or when it goes from no requests to some requests. 

-- Procedure 5:
// Procedure 5 contains nearly identical code to Procedure 4, except it is more nuanced in choosing which next floor to go to. 
// Specifically, it chooses a new request based on the direction the elevator is moving. Further, this request is enforcing 
// liveness in that we expect the elevator to prioritize requests in the direction we are moving, and there are infinite
// requests in both directions (infinite counterexamples).



/*------------------------------------*\
|    Model Properties + Verification   |
\*------------------------------------*/


// Property: Movement is only possible when the elevator's door is closed
pred elevatorOnlyMoveWhenDoorClosed[e: Elevator] {
	e.floor != e.floor' => e.door = Closed
}

// Propety: all requests eventually get fulfilled
pred allRequestsFulfilled[e: Elevator] {
	// if a request is in requests, it is eventually not in requests
	always {
		eventually {
			some f: Floor | {
				f in e.requests => f not in e.requests
			}
		}
	} 
}

// Property: init --> elevator doors closed and stay still
pred initElevator[e: Elevator] {
	e.door = Closed and e.floor = e.floor'
}

// Property: always moves or stays still
pred elevatorMovement[e: Elevator] {
	always {
		(e.floor = e.floor') or (e.floor != e.floor')
	}
}

pred elevatorMovesTowardsRequests[e: Elevator] {
   some (e.requests & e.floor.^above) implies {
       eventually (e.lastMove = Up)
   }

   some (e.requests & e.floor.^below) implies {
       eventually (e.lastMove = Down)
   }
}

// door closes in next state after they open
pred doorClosesAfterOpening[e: Elevator] {
	e.door = Open => e.door' = Closed
}

// door shouldn't open if there is no request
pred doorOpenOnlyWhenRequest[e: Elevator] {
	always {
		(#e.requests = 0) => e.door = Closed
	}
}

pred noPickUpOnNoRequest[e: Elevator] {
	// can't pick up
	eventually {
		pickUp[e]
		no (e.floor & e.requests)
	}
}

pred pickUpOrStayStillRequestOnCurrentFloor[e: Elevator] {
	// if pickUp, then request on current floor
	always {
		pickUp[e] => e.floor in e.requests
	}
}

// elevator moves when door is open
pred elevatorMovesWhenDoorOpen[e: Elevator] {
	eventually {
		e.door = Open
		e.door' = Open
		e.floor != e.floor'
	}
}

pred doorsAlwaysOpen[e: Elevator] {
	always (e.door = Open)
}

-- sat testing preds
pred elevatorNeverMoves[e: Elevator] {
	always (e.floor = Bottom)
}

pred doorsNeverOpen[e: Elevator] {
	always (e.door = Closed)
}

pred doorsEventuallyOpen[e: Elevator] {
	eventually (e.door = Open)
}


test expect {
	// vacuity
	vacuity: {traces} for exactly 1 Elevator is sat 

	// sat tests
	doorsOpen: {traces implies doorsEventuallyOpen[Elevator]} for exactly 1 Elevator is sat
	noMoving: {traces implies elevatorNeverMoves[Elevator]} for exactly 1 Elevator is sat
	doorsStayClosed: {traces implies doorsNeverOpen[Elevator]} for exactly 1 Elevator is sat
	doorsOpen: {traces implies doorsEventuallyOpen[Elevator]} for exactly 1 Elevator is sat

	// theorem tests
	moveWhenDoorClosed: {traces implies elevatorOnlyMoveWhenDoorClosed[Elevator]} for exactly 1 Elevator is theorem
	moveOrStill: {traces implies elevatorMovement[Elevator]} for exactly 1 Elevator is theorem
	doorOpens: {traces implies doorOpenOnlyWhenRequest[Elevator]} for exactly 1 Elevator is theorem
	movesTowards: {traces implies elevatorMovesTowardsRequests[Elevator]} for exactly 1 Elevator is theorem
	pickUpOrStayStill: {traces implies pickUpOrStayStillRequestOnCurrentFloor[Elevator]} for exactly 1 Elevator is theorem
	doorClosedAfterOpen: {traces implies doorClosesAfterOpening[Elevator]} for exactly 1 Elevator is theorem
	
	// unsat tests
	noPickupWORequest: {traces and noPickUpOnNoRequest[Elevator]} for exactly 1 Elevator is unsat
	moveWhenDoorOpen: {traces and elevatorMovesWhenDoorOpen[Elevator]} for exactly 1 Elevator is unsat
	doorStaysOpen: {traces and doorsAlwaysOpen[Elevator]} for exactly 1 Elevator is unsat
}


/*-------------------------------------------------*\
|    Elevator Procedure Properties + Verification   |
\*-------------------------------------------------*/

// Property: forward progress is always possible
pred forwardProgress[e: Elevator] {
	always eventually enabled[e]
}

pred allRequestsCompleted[e: Elevator] {
	all f: Floor | {
		f in (e.requests) => {
			eventually {
				f not in (e.requests)
			} 
		}
	}
}

pred requestRightAboveOrBelow[e: Elevator] {
	always eventually {
		// if some request above, then the floor in the next state is in the requests above
		some (e.requests' & e.floor.^above) => e.floor' in (e.requests' & e.floor.^above) 
		some (e.requests' & e.floor.^below) => e.floor' in (e.requests' & e.floor.^below)
	}
}

pred alwaysStayStillWithNoRequests[e: Elevator] {
	always {
		#e.requests = 0
		e.floor = e.floor' and e.door = Closed and e.door' = Closed
	}
}

pred alwaysStayStill[e: Elevator] {
	always {
		e.floor = e.floor' and e.door = Closed and e.door' = Closed
	}
}

pred alwaysMoveUpOrDown[e: Elevator] {
	always {
		e.lastMove = Up or e.lastMove = Down 

		eventually {
			e.floor = Top
		}

		eventually {
			e.floor = Bottom
		}
	}
}

pred stayStillWithNoRequests[e: Elevator] {
	always {
		#e.requests = 0 => e.floor = e.floor' and e.door = Closed and e.door' = Closed
	}
}

pred eventuallyNoRequests[e: Elevator] {
	eventually {
		#e.requests = 0
	}
}

// Property: nextRequest below but moving up
pred nextRequestBelowButMovingUp[e: Elevator] {
	eventually {
		// open and close
		e.door = Closed 
		e.door' = Closed
		(e.lastMove = Up and e.lastMove' = Up)
		// next request is below	
		e.nextRequest in e.floor.^below
	}
}

pred moveToBottomNoRequests[e: Elevator] {
	always {
		(e.floor != Bottom and #e.requests = 0) => {
			eventually {
				e.floor = Bottom
			}
		}
	}
}

pred notMovesDownWhenRequestAbove[e: Elevator] {
	(e.nextRequest in e.floor.^above) => not moveDown[e] until (e.nextRequest not in e.floor.^above)
}

pred onlyGoesToTopWhenInRequests[e: Elevator] {
	e.floor = Top implies {
		once (Top in e.requests)
	}
}

pred continuesInSameDirection[e: Elevator] {
	pickUpEnabled[e] and (e.nextRequest = e.floor) => {
		e.lastMove = Up => {
			some (e.requests' & e.floor.^above) => e.nextRequest' in (e.requests' & e.floor.^above)
		} else {
			some (e.requests' & e.floor.^below) => e.nextRequest' in (e.requests' & e.floor.^below)
		}
	}
}

test expect {	
	// vacuity
	vacuity: {traces and always procedure1[Elevator]} for exactly 1 Elevator is sat

	// sat tests
	reqAboveorBelow: {traces and always procedure1[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat
	allCompleted: {traces and always procedure1[Elevator] implies allRequestsCompleted[Elevator]} for exactly 1 Elevator is sat
	nxtReqBelowMovingUp: {traces and always procedure1[Elevator] implies nextRequestBelowButMovingUp[Elevator]} for exactly 1 Elevator is sat
	noRequests: {traces and always procedure1[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is sat
	alwaysStillNoRequests: {traces and always procedure1[Elevator] implies alwaysStayStillWithNoRequests[Elevator]} for exactly 1 Elevator is sat
	allStayStill: {traces and always procedure1[Elevator] implies alwaysStayStill[Elevator]} for exactly 1 Elevator is sat

	// eventuallyBottom: {traces and always procedure1[Elevator] implies moveToBottomNoRequests[Elevator]} for exactly 1 Elevator is theorem
	// noRequests: {traces and always procedure1[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is theorem
	fp1: {traces and always procedure1[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	// alwaysMove: {traces and always procedure1[Elevator] implies alwaysMoveUpOrDown[Elevator]} for exactly 1 Elevator is theorem
	stayStillNoRequests: {traces and always procedure1[Elevator] implies stayStillWithNoRequests[Elevator]} for exactly 1 Elevator is theorem
	// notMovesDownWhenRequestAbove1: {traces and always procedure1[Elevator] implies notMovesDownWhenRequestAbove[Elevator]} for exactly 1 Elevator is theorem
	topWasInRequests1: {traces and always procedure1[Elevator] implies always onlyGoesToTopWhenInRequests[Elevator]} for exactly 1 Elevator is theorem
	// continuesInSameDirection1: {traces and always procedure1[Elevator] implies always continuesInSameDirection[Elevator]} for exactly 1 Elevator is theorem

}

test expect {
	// vacuity
	vacuity: {traces and always procedure2[Elevator]} for exactly 1 Elevator is sat

	// sat tests
	reqAboveorBelow: {traces and always procedure2[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat
	allCompleted: {traces and always procedure2[Elevator] implies allRequestsCompleted[Elevator]} for exactly 1 Elevator is sat
	nxtReqBelowMovingUp: {traces and always procedure2[Elevator] implies nextRequestBelowButMovingUp[Elevator]} for exactly 1 Elevator is sat
	noRequests: {traces and always procedure2[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is sat
	alwaysStillNoRequests: {traces and always procedure2[Elevator] implies alwaysStayStillWithNoRequests[Elevator]} for exactly 1 Elevator is sat
	allStayStill: {traces and always procedure2[Elevator] implies alwaysStayStill[Elevator]} for exactly 1 Elevator is sat
	noRequests: {traces and always procedure2[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is sat
	reqAboveorBelow: {traces and always procedure2[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat

	eventuallyBottom: {traces and always procedure2[Elevator] implies moveToBottomNoRequests[Elevator]} for exactly 1 Elevator is theorem
	fp2: {traces and always procedure2[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	alwaysMove: {traces and always procedure2[Elevator] implies alwaysMoveUpOrDown[Elevator]} for exactly 1 Elevator is theorem
	// stayStillNoRequests: {traces and always procedure2[Elevator] implies stayStillWithNoRequests[Elevator]} for exactly 1 Elevator is theorem
	notMovesDownWhenRequestAbove2: {traces and always procedure2[Elevator] implies notMovesDownWhenRequestAbove[Elevator]} for exactly 1 Elevator is theorem
	// topWasInRequests2: {traces and always procedure2[Elevator] implies always onlyGoesToTopWhenInRequests[Elevator]} for exactly 1 Elevator is theorem
	// continuesInSameDirection2: {traces and always procedure2[Elevator] implies always continuesInSameDirection[Elevator]} for exactly 1 Elevator is theorem
}

test expect {
	// vacuity
	vacuity: {traces and always procedure3[Elevator]} for exactly 1 Elevator is sat

	// sat tests
	allCompleted: {traces and always procedure3[Elevator] implies allRequestsCompleted[Elevator]} for exactly 1 Elevator is sat
	reqAboveorBelow: {traces and always procedure3[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat
	nxtReqBelowMovingUp: {traces and always procedure3[Elevator] implies nextRequestBelowButMovingUp[Elevator]} for exactly 1 Elevator is sat
	alwaysStillNoRequests: {traces and always procedure3[Elevator] implies alwaysStayStillWithNoRequests[Elevator]} for exactly 1 Elevator is sat
	alwaysStill: {traces and always procedure3[Elevator] implies alwaysStayStill[Elevator]} for exactly 1 Elevator is sat
	noRequests: {traces and always procedure3[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is sat
	reqAboveorBelow: {traces and always procedure3[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat


	// eventuallyBottom: {traces and always procedure3[Elevator] implies moveToBottomNoRequests[Elevator]} for exactly 1 Elevator is theorem
	fp3: {traces and always procedure3[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	// alwaysMove: {traces and always procedure3[Elevator] implies alwaysMoveUpOrDown[Elevator]} for exactly 1 Elevator is theorem
	stayStillNoRequests: {traces and always procedure3[Elevator] implies stayStillWithNoRequests[Elevator]} for exactly 1 Elevator is theorem
	notMovesDownWhenRequestAbove3: {traces and always procedure3[Elevator] implies notMovesDownWhenRequestAbove[Elevator]} for exactly 1 Elevator is theorem
	topWasInRequests3: {traces and always procedure3[Elevator] implies always onlyGoesToTopWhenInRequests[Elevator]} for exactly 1 Elevator is theorem
	continuesInSameDirection3: {traces and always procedure3[Elevator] implies always continuesInSameDirection[Elevator]} for exactly 1 Elevator is theorem
}

test expect {
	// vacuity
	vacuity: {traces and always procedure4[Elevator]} for exactly 1 Elevator is sat

	// sat tests
	reqAboveorBelow: {traces and always procedure4[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat
	allCompleted: {traces and always procedure4[Elevator] implies allRequestsCompleted[Elevator]} for exactly 1 Elevator is sat
	nxtReqBelowMovingUp: {traces and always procedure4[Elevator] implies nextRequestBelowButMovingUp[Elevator]} for exactly 1 Elevator is sat
	alwaysStillNoRequests: {traces and always procedure4[Elevator] implies alwaysStayStillWithNoRequests[Elevator]} for exactly 1 Elevator is sat
	alwaysStill: {traces and always procedure4[Elevator] implies alwaysStayStill[Elevator]} for exactly 1 Elevator is sat
	noRequests: {traces and always procedure4[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is sat

	eventuallyBottom: {traces and always procedure4[Elevator] implies moveToBottomNoRequests[Elevator]} for exactly 1 Elevator is theorem
	fp4: {traces and always procedure4[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	// alwaysMove: {traces and always procedure4[Elevator] implies alwaysMoveUpOrDown[Elevator]} for exactly 1 Elevator is theorem
	stayStillNoRequests: {traces and always procedure4[Elevator] implies stayStillWithNoRequests[Elevator]} for exactly 1 Elevator is theorem
	notMovesDownWhenRequestAbove4: {traces and always procedure4[Elevator] implies notMovesDownWhenRequestAbove[Elevator]} for exactly 1 Elevator is theorem
	topWasInRequests4: {traces and always procedure4[Elevator] implies always onlyGoesToTopWhenInRequests[Elevator]} for exactly 1 Elevator is theorem
	// continuesInSameDirection4: {traces and always procedure4[Elevator] implies always continuesInSameDirection[Elevator]} for exactly 1 Elevator is theorem
}

test expect {
	vacuity: {traces and always procedure5[Elevator]} for exactly 1 Elevator is sat
	allCompleted: {traces and always procedure5[Elevator] implies allRequestsCompleted[Elevator]} for exactly 1 Elevator is sat
	reqAboveorBelow: {traces and always procedure5[Elevator] implies requestRightAboveOrBelow[Elevator]} for exactly 1 Elevator is sat
	nxtReqBelowButMovingUp: {traces and always procedure5[Elevator] implies nextRequestBelowButMovingUp[Elevator]} for exactly 1 Elevator is sat
	noRequests: {traces and always procedure5[Elevator] implies eventuallyNoRequests[Elevator]} for exactly 1 Elevator is sat
	alwaysStillNoRequests: {traces and always procedure5[Elevator] implies alwaysStayStillWithNoRequests[Elevator]} for exactly 1 Elevator is sat
	alwaysStill: {traces and always procedure5[Elevator] implies alwaysStayStill[Elevator]} for exactly 1 Elevator is sat

	eventuallyBottom: {traces and always procedure5[Elevator] implies moveToBottomNoRequests[Elevator]} for exactly 1 Elevator is theorem
	fp5: {traces and always procedure5[Elevator] implies forwardProgress[Elevator]} for exactly 1 Elevator is theorem
	// alwaysMove: {traces and always procedure5[Elevator] implies alwaysMoveUpOrDown[Elevator]} for exactly 1 Elevator is theorem
	stayStillNoRequests: {traces and always procedure5[Elevator] implies stayStillWithNoRequests[Elevator]} for exactly 1 Elevator is theorem
	notMovesDownWhenRequestAbove5: {traces and always procedure5[Elevator] implies notMovesDownWhenRequestAbove[Elevator]} for exactly 1 Elevator is theorem
	topWasInRequests5: {traces and always procedure5[Elevator] implies always onlyGoesToTopWhenInRequests[Elevator]} for exactly 1 Elevator is theorem
	continuesInSameDirection5: {traces and always procedure5[Elevator] implies always continuesInSameDirection[Elevator]} for exactly 1 Elevator is theorem
}


/*-------------------------------------*\
|    Challenge Problem: Two Elevators   |
\*-------------------------------------*/

-- This predicate is meant to help test various procedures:
--   just change which procedure is being called here (in one place)
--   and the controller will follow suit.
pred runElevatorProcedure[e: Elevator] {
	// can be any procedure
	procedure5[e]
}

// -- The controller, depending on its own needs (which are incomprehensible to
// --   mortals and people who work in the CIT) will allow some elevator(s) to go
// --   in every state (but not necessarily all of them).
// -- This predicate is needed for the challenge problem, but not sooner. 
pred elevatorControl {
	traces
	always {some e: Elevator | runElevatorProcedure[e]}
    always {all e: Elevator | not runElevatorProcedure[e] => stayStill[e]}
}

pred fairnessForProcedure {
	// fair because we can eventually run the procedure in question
	all e: Elevator | {
		// eventually, always possible to be enabled (elevator avoid deadlock)
		(eventually always enabled[e]) => {
			// always can eventually run the procedure in question
			always eventually runElevatorProcedure[e]
		}
	}
}

-- TODO: Test your constraint on predicates from the previous tasks.
test expect {
	// for all elevators, all requests are completed (infinite counerexamples and expect it to eventually happen)
	liveness: {(elevatorControl and fairnessForProcedure) => (all e: Elevator | allRequestsCompleted[e])} for exactly 2 Elevator is theorem
	// for all elevators, can make forward progress (finite counterexamples)
	safety: {(elevatorControl and fairnessForProcedure) => (all e: Elevator | forwardProgress[e])} for exactly 2 Elevator is theorem
}