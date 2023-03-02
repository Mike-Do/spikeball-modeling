#lang forge/bsl

open "spikeball.frg"

test suite for TransitionStates {
    assert SBValidStates is necessary for TransitionStates
    for 10 SBState, exactly 4 Player, exactly 2 Team, 7 Int 
    for {next is linear}
}

test suite for SBinitState {
    example validSBinitState is {some s: SBState | SBinitState[s]} for {
        // Give bounds to the Sigs
        SBState = `S0
        next = `S0 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // scores are 0, Team1 starts with the ball, ball is in right position, and possession is with Team1
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0
        serving_team = `S0 -> `Team1
        ball = `S0 -> `North
        possession = `S0 -> `Team1
    }

    example team2StartsWithBall is {some s: SBState | SBinitState[s]} for {
        // Give bounds to the Sigs
        SBState = `S0
        next = `S0 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // scores are 0, Team2 starts with the ball, ball is in right position, and possession is with Team2
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0
        serving_team = `S0 -> `Team2
        ball = `S0 -> `South
        possession = `S0 -> `Team2
    }

    example invalidSBinitState is not {some s: SBState | SBinitState[s]} for {
        // Give bounds to the Sigs
        SBState = `S0
        next = `S0 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // score starts at 1 for Team 2
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1
        serving_team = `S0 -> `Team1
        ball = `S0 -> `North
        possession = `S0 -> `Team1
    }

    // score starts at 1 for Team 1
    example team1Score1 is not {some s: SBState | SBinitState[s]} for {
        // Give bounds to the Sigs
        SBState = `S0
        next = `S0 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // score starts at 1 for Team 1
        score = `S0 -> `Team1 -> 1 + `S0 -> `Team2 -> 0
        serving_team = `S0 -> `Team1
        ball = `S0 -> `North
        possession = `S0 -> `Team1
    }

    //  score out of bounds (we are considering up to 2)
    example scoreOutOfBounds is not {some s: SBState | SBinitState[s]} for {
        // Give bounds to the Sigs
        SBState = `S0
        next = `S0 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // score starts at 1 for Team 1
        score = `S0 -> `Team1 -> 3 + `S0 -> `Team2 -> 0
        serving_team = `S0 -> `Team1
        ball = `S0 -> `North
        possession = `S0 -> `Team1
    }

    // score negative
    example scoreNegative is not {some s: SBState | SBinitState[s]} for {
        // Give bounds to the Sigs
        SBState = `S0
        next = `S0 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // score starts at 1 for Team 1
        score = `S0 -> `Team1 -> -1 + `S0 -> `Team2 -> 0
        serving_team = `S0 -> `Team1
        ball = `S0 -> `North
        possession = `S0 -> `Team1
    }
}

test suite for SBfoulTransition {
    example validFoulTransition is {some pre, post: SBState | SBfoulTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // test specific definitions
        ball = `S0 -> `South + `S1 -> `Net
        num_touches = `S0 -> 3 + `S1 -> 3
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 1 + `S1 -> `Team1 -> 1 + `S0 -> `Team2 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team2 + `S1 -> `Team2
        possession = `S0 -> `Team2 + `S1 -> `Team2
    }

    example invalidFoulTransition is not {some pre, post: SBState | SBfoulTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // test specific definitions
        ball = `S0 -> `South + `S1 -> `Ground
        num_touches = `S0 -> 3 + `S1 -> 3
        is_serving = `S0 -> 0 + `S1 -> 0

        // Team 2 gained a point after the foul move
        score = `S0 -> `Team1 -> 1 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team2 + `S1 -> `Team2
        possession = `S0 -> `Team2 + `S1 -> `Team2
    }
}

test suite for SBgroundTransition {
        // Team1 scores, They Serve in post state, and they get possession
    example team1Scores is {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Ground + `S1 -> `North
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        // Serve in Post State
        is_serving = `S0 -> 0 + `S1 -> 1
        // Score increase for Team 1
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }

    // Team2 scores, They Serve in post state, and they get possession
    example team2Scores is {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team2 Server
        ball = `S0 -> `Ground + `S1 -> `South
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        // Serve in Post State
        is_serving = `S0 -> 0 + `S1 -> 1
        // Score increase for Team 2
        score = `S0 -> `Team1 -> 1 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team2 + `S1 -> `Team2
        possession = `S0 -> `Team2 + `S1 -> `Team2
    }

    // winning point (Team 1 scores to 2 to win)
    example team1Wins is {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Ground + `S1 -> `North
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        // Serve in Post State
        is_serving = `S0 -> 0 + `S1 -> 1
        // Score increase for Team 1
        score = `S0 -> `Team1 -> 1 + `S0 -> `Team2 -> 1+ `S1 -> `Team1 -> 2 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }

    // serving does not toggle to true in post state
    example invalidServe is not {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Ground + `S1 -> `North
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        // Serve in Post State
        is_serving = `S0 -> 0 + `S1 -> 0
        // Score increase for Team 1
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }

    // Team1 scores, They Serve in post state, and but Team2 gets possession
    example invalidPossession is not {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Ground + `S1 -> `North
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        // Serve in Post State
        is_serving = `S0 -> 0 + `S1 -> 1
        // Score increase for Team 1
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team2
    }

    // Team2 scores, They Serve in post state, and but Team1 gets possession
    example invalidPossession2 is not {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team2 Server
        ball = `S0 -> `Ground + `S1 -> `South
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        // Serve in Post State
        is_serving = `S0 -> 0 + `S1 -> 1
        // Score increase for Team 2
        score = `S0 -> `Team1 -> 1 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 1 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team2 + `S1 -> `Team2
        possession = `S0 -> `Team2 + `S1 -> `Team1
    }
}

test suite for SBnetTransition {
    // Valid
    // Net to North, from Team 2 to Team 1 possession change, score unchanged
    example validNetToNorth is {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team2 Server
        ball = `S0 -> `Net + `S1 -> `North
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 0
        serving_team = `S0 -> `Team2 + `S1 -> `Team2
        possession = `S0 -> `Team2 + `S1 -> `Team1
    }

    // net to south, from Team 1 to Team 2 possession change, score unchanged
    example validNetToSouth is {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Net + `S1 -> `South
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 0
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team2
    }

    // net to east, from Team 1 to Team 2 possession change, score unchanged
    example validNetToEast is {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Net + `S1 -> `East
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 0
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team2
    }

    // net to west, from Team 2 to Team 1 possession change, score unchanged
    example validNetToWest is {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team2 Server
        ball = `S0 -> `Net + `S1 -> `West
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 0
        serving_team = `S0 -> `Team2 + `S1 -> `Team2
        possession = `S0 -> `Team2 + `S1 -> `Team1
    }

    // Num touches does not reset to 0
    example invalidNetToSouth is not {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Net + `S1 -> `South
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 1
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 0
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team2
    }
    // Serving in next state
    example invalidNetToNorth is not {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Net + `S1 -> `North
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 1
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 0
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team2 + `S1 -> `Team1
    }
    // Score randomly changes from net to ground
    example invalidNetToEast is not {some pre, post: SBState | SBnetTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `Net + `S1 -> `East
        // Touches Stay the Same
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team2
    }
}

// test suite for rally
test suite for SBrallyTransition {
    example validSBrallyTransition is {some pre, post: SBState | SBrallyTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `North + `S1 -> `West
        
        // Touches increases by 1
        num_touches = `S0 -> 0 + `S1 -> 1
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }
    
    example invalidSBrallyTransition is not {some pre, post: SBState | SBrallyTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `North + `S1 -> `West
        
        // Touches increases by 1
        num_touches = `S0 -> 0 + `S1 -> 1
        is_serving = `S0 -> 0 + `S1 -> 0

        // score changes incorrectly
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 2
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }

    example invalidSBrallyTransition2 is not {some pre, post: SBState | SBrallyTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Net to Team1 Server
        ball = `S0 -> `North + `S1 -> `West
        
        // Touches doesn't increase (incorrectly)
        num_touches = `S0 -> 0 + `S1 -> 0
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }


    example invalidSBrallyTransition3 is not {some pre, post: SBState | SBrallyTransition[pre, post]} for {
        // Give bounds to the Sigs
        SBState = `S0 + `S1
        next = `S0 -> `S1 + `S1 -> none
        Team = `Team1 + `Team2
        Team1 = `Team1
        Team2 = `Team2
        Player = `Player1 + `Player2 + `Player3 + `Player4
        P1 = `Player1
        P2 = `Player2
        P3 = `Player3
        P4 = `Player4
        Position = `South + `Net + `Ground + `North + `East + `West
        Net = `Net
        Ground = `Ground
        North = `North
        South = `South
        East = `East
        West = `West

        // Position switches incorrectly
        ball = `S0 -> `North + `S1 -> `South
        
        // Touches increases by 1
        num_touches = `S0 -> 0 + `S1 -> 1
        is_serving = `S0 -> 0 + `S1 -> 0
        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1 + `S1 -> `Team1 -> 0 + `S1 -> `Team2 -> 1
        serving_team = `S0 -> `Team1 + `S1 -> `Team1
        possession = `S0 -> `Team1 + `S1 -> `Team1
    }
}