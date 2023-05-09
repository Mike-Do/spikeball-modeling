#lang forge
open "spikeball_two.frg"
// option problem_type temporal
// option max_tracelength 40

-- invokes unsuccessful serve (from server to ground instead of to net)
pred server_to_ground {
    // there exists some state where in the pre the is_serving flag is 1 and in the post the ball is on ground
    some pre, post: SBState {
        post = pre.next
        // SBvalidTransition[pre, post]
        pre.is_serving = 1
        post.ball = Ground
    }
}

-- invokes rally to ground predicate
pred rally_to_ground {
    some pre, post: SBState {
        post = pre.next
        pre.is_serving = 0
        (pre.ball = North or pre.ball = South or pre.ball = West or pre.ball = East)
        pre.num_touches < 3
        post.ball = Ground
    }
}

-- invokes rally to net predicate
pred rally_to_net {
    some pre, post: SBState {
        post = pre.next
        pre.is_serving = 0
        (pre.ball = North or pre.ball = South or pre.ball = West or pre.ball = East)
        pre.num_touches < 3
        post.ball = Net
    }
}

-- invokes foul
pred forced_foul {
    some pre, post: SBState {
        post = pre.next
        pre.is_serving = 0
        (pre.ball = North or pre.ball = South or pre.ball = West or pre.ball = East)
        
        // if num_touches is 3, then the ball must be on the net in the next state
        (pre.num_touches = 3) => {
            post.ball = Net
        }
    }
}

-- the servers on both teams change throughout the game
pred server_changes {
    some pre: SBState {
        pre.server[Team1] != pre.next.server[Team1]
    }

    some pre: SBState {
        pre.server[Team2] != pre.next.server[Team2]
    }
}

-- server switches only when possession changes (the team that had possession and lost a point switches server)
pred server_changes_only_when_possession_changes {
    all pre: SBState {
        // pre.possession is the team that just won a point
        (SBgroundTransition[pre, pre.next] and pre.possession != pre.serving_team) => {
            // the team that served but lost a point switches server
            pre.server[pre.serving_team] != pre.next.server[pre.serving_team]
        }
    }
}


test expect {
    // vacuity: {traces} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat

    // // theorem tests
    // forcedFoul: {traces implies forced_foul} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    switchServer: {traces implies server_changes} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    switchServerOnlyWhenSwitchPossession: {traces implies server_changes_only_when_possession_changes} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    // // sat tests
    // serverToGround: {traces and server_to_ground} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
    // rallyToGround: {traces and rally_to_ground} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
    // rallyToNet: {traces and rally_to_net} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
    
}