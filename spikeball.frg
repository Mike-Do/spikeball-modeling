#lang forge/bsl

// Position Sigs
abstract sig Position {}
one sig Net extends Position {}
one sig Ground extends Position {}
one sig North extends Position {}
one sig South extends Position {}
one sig East extends Position {}
one sig West extends Position {}

// Team Sigs
abstract sig Team {}
one sig Team1 extends Team {
    server: one Person
}
one sig Team2 extends Team {
    server: one Person
}

// Player Sigs
abstract sig Player {
    team: one Team,
    position: one Position
}

one sig P1 extends Player {}
one sig P2 extends Player {}
one sig P3 extends Player {}
one sig P4 extends Player {}

// State sig
sig SBState {
    next: lone State,
    score: pfunc Team -> Int, // score per team
    num_touches: pfunc Team -> Int, //number of touches per team; need to reset
    ball: one Position, // the position of the ball
    possession: one Team,
    serving_team: lone Team
}

// Predicates
pred SBinitState[s: SBState] {
    // set positions for the players
    P1.position = North
    P2.position = West
    P3.position = East
    P4.position = South
    
    // both teams have scores of 0
    s.score[Team1] = 0
    s.score[Team2] = 0
    s.serving_team = Team1    
    Team1.server = P1
    Team2.server = P3
    s.ball = s.serving_team.server.position
    s.possession = s.serving_team
}

pred SBValidStates {
    // Positions of players do not change
    // ball should in one of the positions
    all s: SBState, p: Player | {
        P1.position = North
        P2.position = West
        P3.position = East
        P4.position = South
        s.ball = Net 
    }
}

run {
    // traces
} for exactly 6 State, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear}