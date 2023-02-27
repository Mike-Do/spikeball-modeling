#lang forge/bsl

/*
  Tic-Tac-Toe Model
  (Approximating the live-code version from Spring 2023, for use in lab)  
*/

-- Two players: X and O (their names double as the marks put on the board)
abstract sig Player {}
one sig X, O extends Player {} 

-- Three indexes: A, B, and C (A would be the left column or top row)
abstract sig Index {}
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}

sig Board {
    -- partial function, think of it like a dictionary
    -- For each row and column, we'll have X, O, or none.
    places: pfunc Index -> Index -> Player
}

-- Helper function (in this case, produces an integer)
-- Given a board and player, how many marks has that player made on the board?
fun countPiece[brd: Board, p: Player]: one Int {
  #{r,c: Index | brd.places[r][c] = p}
}

-- Helper predicate (predicates always produce booleans)
-- Is it X's turn in this board?
pred xturn[b: Board] {
  countPiece[b, X] = countPiece[b, O]
} 
-- Is it O's turn in this board?
pred oturn[b: Board] {
  subtract[countPiece[b, X],1] = countPiece[b, O]
}
-- A board is *valid* if it's either X's turn or O's turn
--   (because of how we defined oturn, a board where someone has cheated will be excluded)
pred valid[b: Board] {
  oturn[b] or xturn[b]
}

-- A win for player <p> via a horizontal line
pred winH[b: Board, p: Player] {
  some r: Index | all c: Index |
    b.places[r][c] = p
}

-- A win for player <p> via a vertical line
pred winV[b: Board, p: Player] {
  some c: Index | all r: Index |
    b.places[r][c] = p
}

-- A win for player <p> via a diagonal line
pred winD[b: Board, p: Player] {
    (b.places[A][A] = p and 
     b.places[B][B] = p and
     b.places[C][C] = p)
    or
    (b.places[A][C] = p and 
     b.places[B][B] = p and
     b.places[C][A] = p)
}
-- a win for player <p> via any of the above kinds of line       
pred winning[b: Board, p: Player] {
  winH[b, p] or winV[b, p] or winD[b, p]
}

------------------------------------------------------------------------------

-- When is a board an allowed starting state?
pred init[brd: Board] {
    -- can only start a game with the empty board
	all r, c: Index | no brd.places[r][c]
}

-- When can one board transition to another, according to the rules of the game?
--    (Only on a move: <p> placing their mark at position <r> <c>)
pred move[pre: Board, post: Board, p: Player, r: Index, c: Index] {
    -- GUARD (required to be able to make the move): 
    no pre.places[r][c]         -- no move there yet
    (p = X) implies xturn[pre]    -- correct turn
    p = O implies oturn[pre]    -- correct turn
	-- TRANSITION (what does the post-move board look like?)
    --     Add the mark:
	post.places[r][c] = p    
    --     Assert that no other squares change (this is called a "frame condition"):
    all r2, c2: Index | (r2!=r or c2!=c) implies {
        post.places[r2][c2] = pre.places[r2][c2]
    }
}

------------------------------------------------------------------------------

-- Conjecture: a valid board cannot move to become invalid.
-- Ask Forge to find a pair of boards: pre and post, where pre is valid, 
-- pre moves to post, and post is invalid.
// run {    
//     some pre, post: Board | {
//         valid[pre]
//         not valid[post]
//         some row, col: Index, p: Player |  {
//             move[pre, post, p, row, col]
//         }
//     }
// } 
// -- Allow 2 boards to exist, 3 indexes, and 2 players
// for 2 Board, 3 Index, 2 Player 

-- The above should be unsatisfiable (or "UNSAT")

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- LAB BEGINS (Forge part)
------------------------------------------------------------------------------

-- (1) Read the provided code from above! You will use the predicates we have provided to fill in the run statements below.
--     Take your time in understanding the model. If you have any questions that you can't resolve with your partners, call over
--     a TA to discuss (using the hours queue)

-- (2) Is it possible for a valid board to have _both_ X and O as winners?
run {    
    some board: Board | {
        valid[board]
        winning[board, X]
        winning[board, O]
    }
} for 1 Board, 3 Index, 2 Player  

-- (3) Starting from the initial state, observe unique moves from the first player.
--    Hint: Use the Next button in the visualizer.
// run {    
//   some pre, post: Board  | {
//     init[pre]
//     some row, col: Index, p: Player |  {
//       move[pre, post, p, row, col]
//     }
//   }
// } for 2 Board, 3 Index, 2 Player  

-- (4) What would happen if you rewrote the move predicate in a different way? 
--   Concretely, since there are only two players, it might seem OK to change the:
--       p = X implies xturn[pre]    
--       p = O implies oturn[pre]
--   to just:
--       p = X implies xturn[pre]
--   Is the version with both lines equivalent to the version with only one? Ask Forge to check.
--   Hint: write a new predicate containing the new change, and use a run command to compare them.
// pred changedMove[pre: Board, post: Board, p: Player, r: Index, c: Index] {
//     -- GUARD (required to be able to make the move): 
//     no pre.places[r][c]         -- no move there yet
//     p = X implies xturn[pre]    -- correct turn
// 	  -- TRANSITION (what does the post-move board look like?)
//     --     Add the mark:
// 	  post.places[r][c] = p    
//     --     Assert that no other squares change (this is called a "frame condition"):
//     all r2, c2: Index | (r2!=r or c2!=c) implies {
//         post.places[r2][c2] = pre.places[r2][c2]
//     }
// }

// run {
//     some pre, post: Board  | {
//       init[pre]
//       valid[pre]
//       some row, col: Index, p: Player |  {
//         // Hey Forge, check if the two predicates are equivalent
//         not move[pre, post, p, row, col]
//         changedMove[pre, post, p, row, col]
//       }
//       // check if can move, but not changed move
//       // ask Forge for an instance where one predicate is true (move[...]) and the other is false (not move[...]).
//   }
// } for 2 Board, 3 Index, 2 Player  

-- (4.5) View the instance that Forge produces for the above run. Investigate why the two predicates
-- are not equivalent, and then explain your reasoning in the comment below:

/*
  The changedMove predicate does not check if the player is O with the IMPLIES operator.
  This means that if the player is O, the changedMove predicate will be true even if it is not the O player's turn, 
  even though 
  This is not the case for the move predicate, which checks if it is the O player's turn.
  Therefore, the two predicates are not equivalent.
*/

