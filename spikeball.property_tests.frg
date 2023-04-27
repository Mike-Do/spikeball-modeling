#lang forge
open "spikeball.frg"
option problem_type temporal

-- Team 1 or Team 2 always wins [THEOREM]
pred always_team_one_or_two_wins[s: SBState] {
    always {
        eventually (s.score[Team1] = 2 or s.score[Team2] = 2)
    }
}

-- Team one always wins [UNSAT]
pred team_one_always_wins[s: SBState] {
    always {
        eventually s.score[Team1] = 2 
    }
}

-- Team two always wins [UNSAT]
pred team_two_always_wins[s: SBState] {
    always {
        eventually s.score[Team2] = 2
    }
}

-- The team that serves always wins
// pred serving_team_always_wins[s: SBState] {
//     always {
//         eventually s.score[s.serving_team] = 2
//     }
// }

-- The team that doesn't serve always wins
// pred non_serving_team_always_wins[s: SBState] {
//     always {
//         eventually s.score[s.non_serving_team] = 2
//     }
// }


// The game will always maximum 3 touches (never less than 3 touches) (SARAH)
// pred max_3_touches[] {

// }


// Check that it’s possible for both teams to have 0 touches (SARAH)


// If a team gets a score, it's always from the net to the ground
    --Haley


// Players stay in their cardinal positions (P1 always North…
    --Haley


// The serving team doesn’t stay the same throughout the game -- Mike✅ 


// Check that it’s possible for both teams get at least one point (instead of one team gets 2 points and the other team has no point)s -- Mike✅ 

test expect {
    // 7 is the min number of states for satsfiablility
    -- ✅ ✅ ✅ 
    // vacuity: {traces} for 7 SBState, exactly 4 Player, exactly 2 Team, 7 Int is sat
    
    // sat tests
    
    // theorem tests
    teamAlwaysWins: {traces implies always_team_one_or_two_wins[SBState]} for 40 SBState, exactly 4 Player, exactly 2 Team, 7 Int is theorem
    
    // unsat tests
    teamOneAlwaysWins: {traces implies team_one_always_wins[SBState]} for 7 SBState, exactly 4 Player, exactly 2 Team, 7 Int is unsat
    teamTwoAlwaysWins: {traces implies team_two_always_wins[SBState]} for 7 SBState, exactly 4 Player, exactly 2 Team, 7 Int is unsat
    
}