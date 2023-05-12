#lang forge

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
    server: pfunc Team -> Player,
    is_serving: one Int
}

-- Initializes the state of the game 
pred SBinitState[s: SBState] {
    // both teams have scores of 0
    all t: Team {
        s.score[t] = 0
    }

    // start with serving and no touches
    s.is_serving = 1
    s.num_touches = 0
    
    // either team can start serving
    (s.serving_team = Team1 or s.serving_team = Team2)
    
    // assign ball to the correct server
    s.serving_team = Team1 => {
        s.ball = North
    } else {
        s.ball = South
    }

    // initial servers for the teams
    s.server[Team1] = P1
    s.server[Team2] = P4
    
    // assign possession to the correct serving team
    s.possession = s.serving_team
}

-- Ensures that the state of the game is valid
pred SBValidStates {
    all s: SBState | {
        // ball should in one of the positions
        (s.ball = Net or s.ball = Ground or s.ball = North or s.ball = South or s.ball = East or s.ball = West)

        // one team should have possession at all times
        (s.possession = Team1 or s.possession = Team2)

        // touches should be between 0 and 3
        s.num_touches >= 0
        s.num_touches <= 3

        // either serving or not serving
        (s.is_serving = 0 or s.is_serving = 1)
        // the serving_team should be one of the teams
        (s.serving_team = Team1 or s.serving_team = Team2)
        // the server should be one of the players
        (s.server[Team1] = P1 or s.server[Team1] = P2)
        (s.server[Team2] = P3 or s.server[Team2] = P4)
    }

    // Make sure score is not none and not negative
    all s: SBState, t: Team | {
        some s.score[t] and
        s.score[t] >= 0
    }
}

-- Defines what the final state of the game is
pred SBfinalState[s: SBState] {
    // one team reached the winning score
    #{t: Team | s.score[t] = 2} = 1
    #{t: Team | s.score[t] < 2} = 1
    
    // all scores nonzero
    all t: Team | {
        s.score[t] >= 0
    }

    // constrain touches
    s.num_touches >= 0
    s.num_touches <= 3

    // one of the teams will be serving as a point is awarded from touching the ground in the previous state
    (s.serving_team = Team1 or s.serving_team = Team2)
    
    // ball is necessarily in one of the postions, and is_serving is true
    (s.ball = North or s.ball = South or s.ball = East or s.ball = West)
    (s.is_serving = 1)
}

-- Defines the valid transitions between states
pred SBvalidTransition[pre: State, post: State] {
    // GUARD
    // no one has won yet (has required score)
    all t: Team {
        pre.score[t] >= 0
        pre.score[t] < 2
    }

    // TRANSITION based on cases 
    // If serving, ball hits net or hits the ground (1 attempt allowed)
    (pre.is_serving = 1) => (validServeTransition[pre, post] or invalidServeTransition[pre, post])
    // if ball hits the net
    (pre.ball = Net) => (SBnetTransition[pre, post])
    // hits the ground
    (pre.ball = Ground) => (SBgroundTransition[pre, post])
    // pass to team member
    ((pre.ball = North or pre.ball = South or pre.ball = East or pre.ball = West) and (pre.num_touches < 3) and (pre.is_serving = 0)) => (SBrallyTransition[pre, post] or SBrallyToGroundTransition[pre, post] or SBrallyToNet[pre, post])
    // exceeded 3 touches, foul
    ((pre.ball = North or pre.ball = South or pre.ball = East or pre.ball = West) and (pre.num_touches = 3) and (pre.is_serving = 0)) => (SBfoulTransition[pre, post])
}

-- Defines when a serve hits the net 🎾
pred validServeTransition[pre: State, post: State] {
    // hit to the net
    post.ball = Net
    // is_serving is turns false, and possession stays the same
    pre.possession = post.possession
    post.is_serving = 0

    // number of touches stay the same
    pre.num_touches = post.num_touches

    // score does not change
    all t: Team | {
        pre.score[t] = post.score[t]

        // server stays the same
        pre.server[t] = post.server[t]
    }

    // serving team stays the same
    pre.serving_team = post.serving_team
}

-- Defines when the serve misses the net 🎾
pred invalidServeTransition[pre: State, post: State] {
    // hit to the ground
    post.ball = Ground
    
    // switch possession
    pre.possession != post.possession

    // is_serving triggered again in ground to server transition
    post.is_serving = 0
    
    // number of touches stay the same
    pre.num_touches = post.num_touches

    // score does not change
    all t: Team | {
        pre.score[t] = post.score[t]

        // server stays the same
        pre.server[t] = post.server[t]
    }

    // serving team doesn't change (will change in groundTransition)
    pre.serving_team = post.serving_team
}

-- Defines where the ball goes after hitting the net (either ground or another player on opposite team)
pred SBnetTransition[pre: State, post: State] {
    // if the ball hits the net, then the ball will end up in possession of other team
    (pre.possession = Team1) => {
        // ball changes position
        (post.ball = East or post.ball = South or post.ball = Ground)
        
        // if ball goes to the ground, preserve possession (avoid double-changing)
        (post.ball = Ground) => {
            post.possession = pre.possession
        } else {
            // change possession to new team
            post.possession = Team2
        }
        // reset touches
        post.num_touches = 0        
    } else {
        post.ball = West or post.ball = North or post.ball = Ground
        // reset touches
        post.num_touches = 0

        // if ball goes to the ground, preserve possession (avoid double-changing)
        (post.ball = Ground) => {
            post.possession = pre.possession
        } else {
            // change possession to new team
            post.possession = Team1
        }
    }
    
    // is_serving is always false in this transition, and touches doesn't change
    pre.is_serving = 0
    post.is_serving = 0
    pre.num_touches = post.num_touches

    // score does not change
    all t: Team | {
        pre.score[t] = post.score[t]

        // server stays the same
        pre.server[t] = post.server[t]
    }

    // serving team stays the same
    pre.serving_team = post.serving_team
    
}

-- Awards a point to the correct team and ensures that the correct team is serving in the next state
pred SBgroundTransition[pre: State, post: State] {
    // the score increases (point), in next state new serve   
   (pre.possession = Team1) => {
        add[pre.score[Team1], 1] = post.score[Team1]
        pre.score[Team2] = post.score[Team2]
        // post.possession = Team2
    } else {
        add[pre.score[Team2], 1] = post.score[Team2]
        pre.score[Team1] = post.score[Team1]
        // post.possession = Team1
    }

    // the winning team keeps serving (preserves serving team)
    (pre.serving_team = Team1) => {
        (pre.possession = Team1) => {
            post.serving_team = Team1
            post.ball = (post.server[Team1]).position
            // post.ball = Team1.server.position
            post.possession = Team1

            // server stays the same
            pre.server[Team1] = post.server[Team1]
            pre.server[Team2] = post.server[Team2]
        } else {
            post.serving_team = Team2
            post.ball = (post.server[Team2]).position
            //post.ball = Team2.server.position
            post.possession = Team2
            --SWAP SERVE
            // swap servers here
            pre.server[Team1] != post.server[Team1]
            pre.server[Team2] = post.server[Team2]
        }
    } else {
        // Team2 is serving
        (pre.possession = Team2) => {
            post.serving_team = Team2
            post.ball = (post.server[Team2]).position
            // post.ball = Team2.server.position
            post.possession = Team2
            // server stays the same
            pre.server[Team1] = post.server[Team1]
            pre.server[Team2] = post.server[Team2]
        } else {
            post.serving_team = Team1
            post.ball = (post.server[Team1]).position
            // post.ball = Team1.server.position
            post.possession = Team1
            --SWAP SERVE
            // swap servers here
            pre.server[Team1] = post.server[Team1]
            pre.server[Team2] != post.server[Team2]
        }
    }
    
    // now serving
    post.is_serving = 1
    
    // reset touches
    post.num_touches = 0
}

-- Defines how the ball moves between players on the same team
pred SBrallyTransition[pre: State, post: State] {
    // pass to team member, necessariy one of the cardinal directions, increase touches
    // posession does not change
    pre.possession = post.possession
    
    // touches increases
    add[pre.num_touches, 1] = post.num_touches

    // make sure touch increases (XOR)
    pre.num_touches < post.num_touches
    
    // ball's position changes to the position of the other team member
    (pre.ball = North) => (post.ball = West) 
    (pre.ball = West) => (post.ball = North)
    (pre.ball = South) => (post.ball = East)
    (pre.ball = East) => (post.ball = South)   
    
    // serving state does not change
    pre.is_serving = 0 
    post.is_serving = 0

    // score does not change
    all t: Team | {
         pre.score[t] = post.score[t]

         // server stays the same
         pre.server[t] = post.server[t]
    }

    // serving team stays the same
    pre.serving_team = post.serving_team
}

-- Defines behavior for when a teammate does not hit the ball during a rally 🎾
pred SBrallyToGroundTransition[pre: State, post: State] {
    // from team member to ground
    // posession changes
    pre.possession != post.possession

    // touches does not change
    pre.num_touches = post.num_touches
    
    // score does not change
    all t: Team | {
         pre.score[t] = post.score[t]

         // server stays the same
         pre.server[t] = post.server[t]
    }
    
    // The ball is on the Ground in the post state
    post.ball = Ground

    // serving state does not change
    post.is_serving = pre.is_serving

    // serving team stays the same
    pre.serving_team = post.serving_team

}

-- Defines using less than 3 touches to hit to the net 🎾
pred SBrallyToNet[pre: State, post: State] {
    // possession does not change (posession to other team handled by net transition)
    pre.possession = post.possession

    // touches does not change
    pre.num_touches = post.num_touches
    
    // score does not change
    all t: Team | {
         pre.score[t] = post.score[t]

         // server stays the same
         pre.server[t] = post.server[t]
    }
    
    // ball is on net in next state
    post.ball = Net

    // serving state does not change
    pre.is_serving = post.is_serving

    // serving team stays the same
    pre.serving_team = post.serving_team
}

-- Defines behavior for when a team uses their 3 touches and must hit to the net 🎾
pred SBfoulTransition[pre: State, post: State] {
    // hit to the net after 3 touches!
    post.ball = Net
    
    // serving state does not change
    pre.is_serving = 0
    post.is_serving = 0

    // score does not change
    all t: Team | {
         pre.score[t] = post.score[t]
         
         // server stays the same
         pre.server[t] = post.server[t]
    }
    
    // serving team stays the same
    pre.serving_team = post.serving_team
    
    // possession doesn't change
    pre.possession = post.possession
}

-- Defines the valid transitions between states
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

-- Defines the setup of the game
pred SBSetup {
    // define setup of static values throughout the game
    P1.position = North
    P2.position = West
    P3.position = East
    P4.position = South

    P1.team = Team1
    P2.team = Team1
    P3.team = Team2
    P4.team = Team2
}

-- Defines the traces of the game
pred traces {
    SBValidStates
    TransitionStates
    SBSetup
}

run {
    traces
} for 80 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear}