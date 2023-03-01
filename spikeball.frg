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
abstract sig Team {
    server: one Player
}
one sig Team1 extends Team {}
one sig Team2 extends Team {}

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
    next: lone SBState,
    score: pfunc Team -> Int, // score per team
    num_touches: one Int,
    ball: one Position, // the position of the ball
    possession: one Team,
    serving_team: one Team,
    is_serving: one Int
}

// Predicates
pred SBinitState[s: SBState] {
    // set positions for the players
    // P1.position = North
    // P2.position = West
    // P3.position = East
    // P4.position = South
    
    // both teams have scores of 0
    all t: Team {
        s.score[t] = 0
    }

    s.is_serving = 1
    s.num_touches = 0
    s.serving_team = Team1    

    // Team1.server = P1
    // Team2.server = P4
    
    s.ball = North
    s.possession = s.serving_team
}


// TODO: may need to revisit this if a bug arises
pred SBValidStates {
    // Positions of players do not change
    // ball should in one of the positions
    // One team should have possession at all times
    all s: SBState | {
        // P1.position = North
        // P2.position = West
        // P3.position = East
        // P4.position = South
        // Team1.server = P1
        // Team2.server = P4
        (s.ball = Net or s.ball = Ground or s.ball = North or s.ball = South or s.ball = East or s.ball = West)
        (s.possession = Team1 or s.possession = Team2)

        s.num_touches >= 0
        s.num_touches <= 3
        (s.is_serving = 0 or s.is_serving = 1)
    }
}

// pred canServe[s: SBState] {
//     // if the ball is on the ground or we are in the initState
//     (SBinitState[s] or
//     s.ball = Ground)
//     // define who the server is
//     // s.possession = Team1 implies s.serving_team = Team1
//     // s.possession = Team2 implies s.serving_team = Team2    
// }

pred point[pre: SBState, post: SBState] {
    // if ball touches ground, score for team w/o possession
    (pre.ball = Ground) implies {
        // TODO: may have to revisit if error thrown
        (pre.possession = Team1) => (add[pre.score[Team2], 1] = post.score[Team2]) else (add[pre.score[Team1], 1] = post.score[Team1])
    }

    // make sure point has increased for one of the teams (XOR)
    #{t: Team | pre.score[t] < post.score[t]} = 1
}

pred SBfinalState[s: SBState] {
    // one team reached the winning score
    #{t: Team | s.score[t] = 3} = 1
    // s.score[Team1] = 3 or s.score[Team2] = 3
    
    // make sure the score is within bound for both teams
    all t: Team | {
        s.score[t] >= 0
        s.score[t] <= 3
        // s.num_touches[t] <= 0
        // s.num_touches[t] >= 3
    }
    s.num_touches >= 0
    s.num_touches <= 3
    
    // ball is on the ground, awarding the final point
    // s.ball = Ground
}

pred SBvalidTransition[pre: State, post: State] {
    // GUARD
    // no one has won yet (has required score)
    all t: Team {
        pre.score[t] >= 0
        pre.score[t] < 3
    }

    // TRANSITION based on cases 
    
    // If [canServe] in pre state, in post state the ball’s position is on the net, and the possession shifts to the other team
    // If serving, ball hits net!
    (pre.is_serving = 1) => (serveTransition[pre, post])
    // if ball hits the net
    (pre.ball = Net) => (SBnetTransition[pre, post])
    // hits the ground
    (pre.ball = Ground) => (SBgroundTransition[pre, post])
    // pass to team member
    ((pre.ball = North or pre.ball = South or pre.ball = East or pre.ball = West) and (pre.num_touches < 3) and (pre.is_serving = 0)) => (SBrallyTransition[pre, post])
}

// TODO: May need to revisit if overlap between canServe and other predicates, perhaps add a State field to canServe
pred serveTransition[pre: State, post: State] {
    post.ball = Net
    pre.possession = post.possession
    post.is_serving = 0
    // TODO: may have to revisit if error thrown
    // (pre.possession = Team1) => post.possession = Team2 else post.possession = Team1
    pre.num_touches = post.num_touches
}

pred SBnetTransition[pre: State, post: State] {
    // if the ball hits the net, then the ball will end up in possession of other team
    (pre.possession = Team1) => {
        // ball changes position
        post.ball = East or post.ball = South or post.ball = Ground

        // reset touches
        post.num_touches = 0
        // post.num_touches[Team1] = 0
        
        // change possession to new team
        post.possession = Team2
    } else {
        post.ball = West or post.ball = North or post.ball = Ground

        // reset touches
        post.num_touches = 0
        // post.num_touches[Team2] = 0

        // change possession to new team
        post.possession = Team1
    }
    pre.is_serving = post.is_serving
    pre.num_touches = post.num_touches
    // (pre.possession = Team1) => (post.ball = South or post.ball = East or post.ball = Ground) else (post.ball = North or post.ball = West or post.ball = Ground)

    // FOR LATER REFERENCE
    // change possession to new team
    // (pre.possession = Team1) => post.possession = Team2 else post.possession = Team1
}

pred SBgroundTransition[pre: State, post: State] {
    // the score increases (point), in next state new serve
    point[pre, post]
    // poessession changes and ball will in position of server
    (pre.possession = Team1) => {
        post.possession = Team2
        post.serving_team = Team2
        post.ball = Team2.server.position
    } else {
        post.possession = Team1
        post.serving_team = Team1
        post.ball = Team1.server.position
    }
    post.is_serving = 1
    pre.num_touches = post.num_touches
}

pred SBrallyTransition[pre: State, post: State] {
    // pass to team member, necessariy one of the cardinal directions, increase touches
    // posession does not change
    pre.possession = post.possession
    // touches increases
    add[pre.num_touches, 1] = post.num_touches
    // add[pre.num_touches[pre.possession], 1] = post.num_touches[post.possession]

    // make sure touch increases (XOR)
    pre.num_touches < post.num_touches
    
    // ball's position changes to the position of the other team member
    (pre.ball = North) => (post.ball = West)
    (pre.ball = West) => (post.ball = North)
    (pre.ball = South) => (post.ball = East)
    (pre.ball = East) => (post.ball = South)   
    
    // serving state does not change
    pre.is_serving = post.is_serving
}

pred TransitionStates {
    some init, final: SBState {
        SBinitState[init]
        SBfinalState[final]
        all s: SBState {
            init != s implies reachable[s, init, next]
        }

        all s: SBState {
            some s.next implies SBvalidTransition[s, s.next]
        }
    }
}

pred SBSetup {
    P1.position = North
    P2.position = West
    P3.position = East
    P4.position = South

    Team1.server = P1
    Team2.server = P4
    P1.team = Team1
    P2.team = Team1
    P3.team = Team2
    P4.team = Team2
}


run {
    // traces
    SBValidStates
    TransitionStates
    SBSetup
} for exactly 4 Player, exactly 2 Team, 7 Int for {next is linear}