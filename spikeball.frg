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


// TODO: may need to revisit this if a bug arises
pred SBValidStates {
    // Positions of players do not change
    // ball should in one of the positions
    // One team should have possession at all times
    all s: SBState | {
        P1.position = North
        P2.position = West
        P3.position = East
        P4.position = South
        Team1.server = P1
        Team2.server = P3
        (s.ball = Net or s.ball = Ground or s.ball = North or s.ball = South or s.ball = East or s.ball = West)
        (s.possession = Team1 or s.possession = Team2)

        // valid number of touches per team
        s.num_touches[Team1] >= 0
        s.num_touches[Team1] <= 3
        s.num_touches[Team2] >= 0
        s.num_touches[Team2] <= 3
    }
}

pred canServe[s: State] {
    // if the ball is on the ground or we are in the initState
    [SBinitState[s]] or
    s.ball = Ground
    // define who the server is
    s.possession = Team1 implies s.serving_team = Team1
    s.possession = Team2 implies s.serving_team = Team2    
}

pred point[s: State] {
    // if ball touches ground, score for team w/o possession
    s.ball = Ground implies {
        // TODO: may have to revisit if error thrown
        (s.possession = Team1) => (s.score[Team2] = s.score[Team2] + 1) else (s.score[Team1] = s.score[Team1] + 1)
    }
}

pred SBfinalState[s: State] {
    // one team reached the winning score
    s.score[Team1] = 3 or s.score[Team2] = 3
    
    // touches should be less than 3
    s.num_touches[Team1] >= 0
    s.num_touches[Team1] <= 3
    s.num_touches[Team2] >= 0
    s.num_touches[Team2] <= 3
    // ball is on the ground, awarding the final point
    s.ball = Ground
}




run {
    // traces
} for exactly 6 State, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear}