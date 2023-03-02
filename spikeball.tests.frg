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

        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 0
        serving_team = `S0 -> `Team1
        ball = `S0 -> `North
        possession = `S0 -> `Team1
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

        score = `S0 -> `Team1 -> 0 + `S0 -> `Team2 -> 1
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
    example validSBgroundTransition is {some pre, post: SBState | SBgroundTransition[pre, post]} for {
        
    }
}