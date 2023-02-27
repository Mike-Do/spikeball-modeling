#lang forge/bsl

/*
  Tic-tac-toe boards, moves, and games
  Feb 10 Livecode
*/

abstract sig Player {}
one sig X, O extends Player {}

sig Board {
    board: pfunc Int -> Int -> Player
}

pred wellformed[b: Board] {
    all row, col: Int | {
        (row < 0 or row > 2 or col < 0 or col > 2) implies
        no b.board[row][col]
    }
}

// run {
//     some b: Board | wellformed[b]
// } for exactly 1 Board

pred Xturn[b: Board] {
    -- same number of X and O on board
    #{row, col: Int | b.board[row][col] = X} = 
    #{row, col: Int | b.board[row][col] = O}
}

pred Oturn[b: Board] {
    #{row, col: Int | b.board[row][col] = X} = 
    add[#{row, col: Int | b.board[row][col] = O}, 1]
}
pred balanced[b: Board] {
    Oturn[b] or Xturn[b]
}

pred winRow[b: Board, p: Player] {
    some row: Int | {
        b.board[row][0] = p
        b.board[row][1] = p
        b.board[row][2] = p
    }
}

pred winCol[b: Board, p: Player] {
    some col: Int | {
        b.board[0][col] = p
        b.board[1][col] = p
        b.board[2][col] = p
    }
}


pred winner[b: Board, p: Player] {
    winRow[b, p]
    or 
    winCol[b, p]
    or {
      b.board[0][0] = p
      b.board[1][1] = p
      b.board[2][2] = p
    } or {
      b.board[0][2] = p
      b.board[1][1] = p
      b.board[2][0] = p
    }
}

// run {    
//     all b: Board | {
//         -- X has won, and the board looks OK
//         wellformed[b]
//         winner[b, X]
//         balanced[b]
//         -- X started in the middle
//         b.board[1][1] = X
//     }
// } for exactly 2 Board

-------------------------------------------------
-- Games

pred starting[b: Board] {
    all row, col: Int | 
        no b.board[row][col]
}

pred doNothing[pre: Board, post: Board] {
    -- GUARD
    some p: Player | winner[pre, p]

    -- ACTION
    -- TN: notes TODO
    all row2: Int, col2: Int | 
        post.board[row2][col2] = pre.board[row2][col2]

}

pred move[pre: Board, post: Board, row: Int, col: Int, p: Player] {
    -- GUARD (what needs to hold about the pre-state?)
    no pre.board[row][col] -- no move already there
    p = X implies Xturn[pre] -- appropriate turn
    p = O implies Oturn[pre]  
    row <= 2 and row >= 0 
    col <= 2 and col >= 0
    -- No winner yet (guard)
    all p: Player | not winner[pre, p]
    

    -- ACTION (what does the post-state then look like?)
    post.board[row][col] = p
    all row2: Int, col2: Int | (row!=row2 or col!=col2) implies {                
        post.board[row2][col2] = pre.board[row2][col2]     
    }  

}

// Is there a potential issue in this move predicate? Write a 'run' to find it!
// run {
//     -- only show me moves involving well-formed boards
//     all b: Board | wellformed[b]

//     some pre, post: Board | {
//       some row, col: Int, p: Player | {
//         move[pre, post, row, col, p]
//       }
//     }
// } for 2 Board

// run {
//     some pre, post: Board | {
//       wellformed[pre]
//       not wellformed[post]
//       some row, col: Int, p: Player | {
//         move[pre, post, row, col, p]
//       }
//     }
// } for 2 Board

-- Does TTT fail to preserve "X has won"
// run {
//     some pre, post: Board | {
//       winner[pre, X]
//       not winner[post, X]
//       some row, col: Int, p: Player | {
//         move[pre, post, row, col, p]
//       }
//     }
// } for 2 Board

-----------------
-- GAMES

one sig Game {
  initialState: one Board,
  next: pfunc Board -> Board
}

pred traces {
    starting[Game.initialState]
    all b: Board | some Game.next[b] implies {
        some row, col: Int, p: Player | {
            move[b, Game.next[b], row, col, p]            
        }
        or
            doNothing[b, Game.next[b]]
    }
    

    --- ? 
    --- do we need to say that initialState is the first state in "next"
}

run {
    all b: Board | wellformed[b]
    traces
-- } for 6 Board, 3 Int for {next is linear}
} for 10 Board, 3 Int for {next is linear}

