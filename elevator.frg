#lang forge

option problem_type temporal
option max_tracelength 14

-- Do not change anything in this file!

/*---------------*\
|   Definitions   |
\*---------------*/

sig Floor {
	above : lone Floor,
	below : lone Floor
}
one sig Top extends Floor {}
one sig Bottom extends Floor {}

abstract sig Direction {}
one sig Up extends Direction {}
one sig Down extends Direction {}

abstract sig Door {}
one sig Open extends Door {}
one sig Closed extends Door {}

sig Elevator {
	var floor : one Floor,
	var door : one Door,
	var requests : set Floor,
	var nextRequest : one Floor,  // nextRequest and lastMove fields only used in
	var lastMove: one Direction   // procedures 4 and 5, ignore otherwise
}

pred floors {
	-- Top Floor
	no Top.above
	-- Bottom Floor
	no Bottom.below
	-- Connected (could do via either top or bottom)
	all f : Floor | f in Bottom.*above
	-- Ensures above/below relations match up
	~above = below
}



/*-----------------------*\
|   Elevator Operations   |
\*-----------------------*/

pred init[e: Elevator] {
	-- The elevator starts on the bottom with door closed.
	e.floor = Bottom 
	e.door = Closed
	some e.requests => {
		e.nextRequest in e.requests
	} else {
		e.nextRequest = Bottom
	}
	e.lastMove = Up
}

pred moveUpEnabled[e: Elevator] {
	e.floor != Top
	e.door = Closed
}

pred moveUp[e: Elevator] {
	moveUpEnabled[e]
	e.floor' = e.floor.above
	e.door' = Closed
	e.requests in e.requests'
	e.nextRequest' = e.nextRequest
	e.lastMove' = Up
}

pred moveDownEnabled[e: Elevator] {
	e.floor != Bottom
	e.door = Closed
}

pred moveDown[e: Elevator] {
	moveDownEnabled[e]
	e.floor' = e.floor.below
	e.door' = Closed
	e.requests in e.requests'
	e.nextRequest' = e.nextRequest
	e.lastMove' = Down
}

pred openDoorEnabled[e: Elevator] {
	e.floor in e.requests
	e.door = Closed
}

pred openDoor[e: Elevator] {
	openDoorEnabled[e]
	e.floor' = e.floor
	e.door' = Open
	e.requests' = e.requests
	e.nextRequest' = e.nextRequest
	e.lastMove' = e.lastMove
}

pred pickUpEnabled[e: Elevator] {
	e.door = Open
	e.floor in e.requests
}

pred pickUp[e: Elevator] {
	pickUpEnabled[e]
	e.door' = Closed
	e.floor' = e.floor
	e.requests' = e.requests - e.floor
	e.nextRequest = e.floor => {
		// choose a new `nextRequest`
		(some e.requests') => (e.nextRequest' in e.requests') else (e.nextRequest' = Bottom)
	} else {
		e.nextRequest' = e.nextRequest
	}
	e.lastMove' = e.lastMove
}

pred stayStill[e: Elevator] {
	e.floor' = e.floor
	e.door' = Closed
	e.requests in e.requests'
	e.nextRequest' = e.nextRequest
	e.lastMove' = e.lastMove
}

pred enabled[e: Elevator] {
	moveUpEnabled[e] or 
	moveDownEnabled[e] or
	openDoorEnabled[e] or
	pickUpEnabled[e]
}

pred moves[e: Elevator] {
	moveUp[e] or
	moveDown[e] or
	openDoor[e] or
	pickUp[e]
}

-- Helper
pred pickUpCurIfRequesting[e: Elevator] {
	// if current floor is requesting and door is closed, open door
	e.floor in e.requests and e.door = Closed => openDoor[e]

	// if current floor is requesting and door is open, pick up
	pickUpEnabled[e] => pickUp[e]
}

pred traces {
	floors
	all e: Elevator | always {(no e.requests) => e.nextRequest = Bottom}
	all e: Elevator | init[e]
	all e: Elevator | always {moves[e] or stayStill[e]}
}


/*-----------------------*\
|  5 Elevator Procedures  |
\*-----------------------*/


pred procedure1[e: Elevator] {
	// stay still if there are no requests (double implication)
	no e.requests iff stayStill[e]

	// pick up current floor if requesting
	always pickUpCurIfRequesting[e]

	// don't move up if there are lower requests
	some (e.floor.^below & e.requests) => not moveUp[e]

	// don't move down if there are no lower requests
	no (e.floor.^below & e.requests) => not moveDown[e]
}


pred procedure2[e: Elevator] {
	// never stay still
	not stayStill[e]

	// pick up current floor if requesting
	always pickUpCurIfRequesting[e]

	// once at the bottom, move up until the top
	e.floor = Bottom => (not moveDown[e]) until e.floor = Top

	// once at the top, move down until the bottom
	e.floor = Top => (not moveUp[e]) until e.floor = Bottom
}


pred procedure3[e: Elevator] {
	// don't stay still if there are some requests (double implication)
	no e.requests iff stayStill[e]

	// pick up current floor if requesting
 	always pickUpCurIfRequesting[e]

	// when any requests above, move up until no higher requests
	some (e.requests & e.floor.^above) => (not moveDown[e]) until no (e.requests & e.floor.^above)
	
	// when any requests below, move down until no lower requests
	some (e.requests & e.floor.^below) => (not moveUp[e]) until no (e.requests & e.floor.^below)
}


pred procedure4[e: Elevator] {
	// only stay still if there are no requests
	no e.requests iff stayStill[e]

	// always pick up current floor if requesting
	always pickUpCurIfRequesting[e]
	
	// when `nextRequest` is above, move up until it is completed
	(e.nextRequest in e.floor.^above) => not moveDown[e] until (e.nextRequest not in e.floor.^above)
	
	// when `nextRequest` is below, move down until it is completed
	(e.nextRequest in e.floor.^below) => not moveUp[e] until (e.nextRequest not in e.floor.^below)

	// handles case when elevator starts on Bottom with no requests
	(some e.requests) and (e.nextRequest not in e.requests) => e.nextRequest' in e.requests'

	// handles `nextRequest` when elevator goes from no requests to some requests
	((no e.requests) and (some e.requests')) => e.nextRequest' in e.requests'
}


pred procedure5[e: Elevator] {
	// only stay still if there are no requests
	no e.requests iff stayStill[e]

	// always pick up current floor if requesting
	always pickUpCurIfRequesting[e]
	
	// when `nextRequest` is above, move up until it is completed
	(e.nextRequest in e.floor.^above) => not moveDown[e] until (e.nextRequest not in e.floor.^above)
	
	// when `nextRequest` is below, move down until it is completed
	(e.nextRequest in e.floor.^below) => not moveUp[e] until (e.nextRequest not in e.floor.^below)

	// handles case when elevator starts on Bottom with no requests
	(some e.requests) and (e.nextRequest not in e.requests) => e.nextRequest' in e.requests'

	// handles `nextRequest` when elevator goes from no requests to some requests
	((no e.requests) and (some e.requests')) => e.nextRequest' in e.requests'

	// if choosing a new `nextRequest`, choose one higher if moving up and lower if moving down
	pickUpEnabled[e] and (e.nextRequest = e.floor) => {
		e.lastMove = Up => {
			some (e.requests' & e.floor.^above) => e.nextRequest' in (e.requests' & e.floor.^above)
		} else {
			some (e.requests' & e.floor.^below) => e.nextRequest' in (e.requests' & e.floor.^below)
		}
	}
}