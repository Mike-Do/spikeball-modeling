#lang forge
open "spikeball_two.frg"

/*
    Property verification tests for new properties added to Spikeball 2
*/
-- invokes unsuccessful serve (from server to ground instead of to net) [SAT]
pred server_to_ground {
    // there exists some state where in the pre the is_serving flag is 1 and in the post the ball is on ground
    some pre, post: SBState {
        post = pre.next
        // SBvalidTransition[pre, post]
        pre.is_serving = 1
        post.ball = Ground
    }
}

-- invokes rally to ground predicate [SAT]
pred rally_to_ground {
    some pre, post: SBState {
        post = pre.next
        pre.is_serving = 0
        (pre.ball = North or pre.ball = South or pre.ball = West or pre.ball = East)
        pre.num_touches < 3
        post.ball = Ground
    }
}

-- invokes rally to net predicate [SAT]
pred rally_to_net {
    some pre, post: SBState {
        post = pre.next
        pre.is_serving = 0
        (pre.ball = North or pre.ball = South or pre.ball = West or pre.ball = East)
        pre.num_touches < 3
        post.ball = Net
    }
}

-- invokes foul after all 3 touches have been used for rallying [THEOREM]
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

-- the servers on both teams change throughout the game [THEOREM]
pred server_changes {
    some pre: SBState {
        pre.server[Team1] != pre.next.server[Team1]
    }

    some pre: SBState {
        pre.server[Team2] != pre.next.server[Team2]
    }
}

-- server switches only when possession changes (the team that had possession and lost a point switches server) [THEOREM]
pred server_changes_only_when_possession_changes {
    all pre: SBState {
        // pre.possession is the team that just won a point
        (SBgroundTransition[pre, pre.next] and pre.possession != pre.serving_team) => {
            // the team that served but lost a point switches server
            pre.server[pre.serving_team] != pre.next.server[pre.serving_team]
        }
    }
}

/*
    Property verification tests for properties that also existed in Spikeball 1
*/
-- Team 1 or Team 2 always wins [THEOREM]
pred always_team_one_or_two_wins {
    some s: SBState {
        s.score[Team1] = 2 or s.score[Team2] = 2
    }
}

// If a team gets a score, it's always from the ground to a person [THEOREM]
pred score_on_ground_to_server {
    // in some state, the ball is on the ground
    // check if Team1 or Team2 scored
    // in the next state, the ball is either North or South, North if Team1 scored, South if Team2 scored
    some s, snext: SBState {
        snext = s.next
        
        some t: Team {
            (add[s.score[t], 1] = snext.score[t]) => {
                s.ball = Ground
                (t = Team1) => {
                    snext.ball = North
                } else {
                    snext.ball = South
                }
            }
        }
    }
}

test expect {
    vacuity: {traces} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat

    // theorem tests
    forcedFoul: {traces implies forced_foul} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    switchServer: {traces implies server_changes} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    switchServerOnlyWhenSwitchPossession: {traces implies server_changes_only_when_possession_changes} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    alwaysExistsWinningTeam: {traces implies always_team_one_or_two_wins} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
    scoreOnGroundToServer: {traces implies score_on_ground_to_server} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is theorem
   
    // sat tests
    serverToGround: {traces and server_to_ground} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
    rallyToGround: {traces and rally_to_ground} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
    rallyToNet: {traces and rally_to_net} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
}