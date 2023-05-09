// Visualization for TTT
// /*
//   Visualizing the `ttt.frg` model, which produces traces
//   of a tic-tac-toe game. This code uses the April 2023 Sterling 
//   D3FX library. If you want to use D3 directly, see `ttt_old.js`.
// */

// // the stage contains everything in the visualization
// const stage = new Stage()
// const numStates = instance.signature('Board').tuples().length

// // the *outer* grid produces a one-column "film-strip" style 
// // layout for all states in the trace given
// let grid = new Grid({
//   grid_location: {x: 20, y: 20},
//   cell_size: {x_size: 100, y_size: 100},
//   grid_dimensions: {x_size: 1, y_size: numStates }
// })
// stage.add(grid)

// // Create an *inner* grid for every TTT board, placed from
// // top to bottom of the outer grid:
// for(b = 0; b <= 10; b++) {  
//   if(Board.atom("Board"+b) != null)
//     grid.add({x:0, y:b}, makeBoard(Board.atom("Board"+b)))
// }

// function makeBoard(stateAtom) {
//   let innerGrid = new Grid({
//     grid_location: {x: 0, y:0},
//     cell_size: {x_size: 30, y_size: 30},
//     grid_dimensions: {x_size: 3, y_size: 3 }
//   })  
  
//   for (r = 0; r <= 2; r++) {
//     for (c = 0; c <= 2; c++) {
//       const val = stateAtom.board[r][c].toString().substring(0,1)      
//       const tbox = new TextBox({
//         text: `${val}`, 
//         coords: {x:0,y:0}, 
//         color: 'black', 
//         fontSize: 16})
//       innerGrid.add({x: r, y: c}, tbox)
//     } 
//   }
//   return innerGrid
// }

// Visualization for tree
/*
  Tree visualization example for instances of the `tree.frg` model. 
  For a basic version that doesn't rely on Forge instances, see  
  the `tree.js` file instead.
*/

// Step 1: find the root of the binary tree. This will be the `Tree`
// atom without any parent, which we can find by reversing the `left`
// and `right` fields.
// const roots = instance.signature('Tree').tuples().filter(t => {
//     return (left.join(t).tuples().length < 1) &&
//            (right.join(t).tuples().length < 1)
// })
// const root = roots[0]

// // Note: if you are trying to do something like the above, and get an 
// // error message like "[dot join] tried to join tree with filter, 
// // but no set filter defined", check that you haven't forgotten to
// // call .tuples() on the sig. The sig itself isn't an array.

// // Step 2: construct the tree structure recursively 
// const visTree = buildTree(root)

// function buildLeaf() {
//     // Each leaf should be a distinct primitive object
//     return {
//         visualObject: new Circle({radius: 5, color: 'black'}),
//         children: []
//     }
// }

// function buildTree(t) {    
//     const myValue = t.join(val)
//     const myLeftTuples = t.join(left).tuples()
//     const myRightTuples = t.join(right).tuples()
//     const obj = new Circle({
//         radius: 20, 
//         borderColor: "black", 
//         color: "white", 
//         // For debugging:
//         //label: `${myValue};${t}`});    
//         // For final visualization:
//         label: `${myValue}`});
        
//     // If this node has left/right children, build their subtree structure
//     const leftSubtree = myLeftTuples.length > 0 ? 
//                         [buildTree(myLeftTuples[0])] : 
//                         [buildLeaf()]
//     const rightSubtree = myRightTuples.length > 0 ? 
//                         [buildTree(myRightTuples[0])] : 
//                         [buildLeaf()]
//     return {
//         visualObject: obj,
//         // Using ... will collapse to empty array if there are no children
//         children: [...leftSubtree, ...rightSubtree]
//     }
// }

// // Note: if you are trying to do something like the above helper, and 
// // get a TypeError about the function parameter being undefined, be 
// // aware that JavaScript may be reporting that the value `undefined`
// // was passed in, and is being used unsafely---not that somehow the
// // parameter name isn't recognized!



// // Create a compound tree object with the above structure
// let tree = new Tree({
//     root: visTree, 
//     height: 200, 
//     width: 300, 
//     coords: { x: 100, y: 100 }
//     });

// // Finally, add to the stage and render it
// stage = new Stage()
// stage.add(tree)
// stage.render(svg)

// // Finally, render the stage
// stage.render(svg, document)

// SIGS
// abstract sig Position {}
// one sig Net extends Position {}
// one sig Ground extends Position {}
// one sig North extends Position {}
// one sig South extends Position {}
// one sig East extends Position {}
// one sig West extends Position {}

// // Team Sigs
// abstract sig Team {
//     server: one Player
// }
// one sig Team1 extends Team {}
// one sig Team2 extends Team {}

// // Player Sigs
// abstract sig Player {
//     team: one Team,
//     position: one Position
// }

// one sig P1 extends Player {}
// one sig P2 extends Player {}
// one sig P3 extends Player {}
// one sig P4 extends Player {}

// Write a visualization for the Spikball model.
// There are 4 players, each with a position of North, South, East, or West.
// The net is in the middle of the field.
// The ball either moves between players, the net, or the ground (make it appear as a circle)
// Add text for the score for both Teams, and the number of touches
// Make the players on same team the same color (Red or Blue)

// Define stage
const stage = new Stage()
const numStates = instance.signature('SBState').tuples().length

// Define outer grid
let grid = new Grid({
    grid_location: {x: 20, y: 20},
    cell_size: {x_size: 400, y_size: 400},
    grid_dimensions: {x_size: 1, y_size: numStates }
})

stage.add(grid)

// create an inner 3x3 grid for each state, specify North, South, East, West on the grid, and net in the middle
for (b = 0; b <= 39; b++) {
    // for each state, add the inner grid
    if(SBState.atom("SBState"+b) != null)
        grid.add({x:0, y:b}, makeBoard(SBState.atom("SBState"+b)))
}

function makeP1() {
    const obj = new Circle({
        radius: 30,
        borderColor: "black",
        // red
        color: "#FAA0A0",
        label: "P1",
        fontSize: 16
    })
    return obj
}

function makeP2() {
    const obj = new Circle({
        radius: 30,
        borderColor: "black",
        // red
        color: "#FAA0A0",
        label: "P2",
        fontSize: 16
    })
    return obj
}

function makeP3() {
    const obj = new Circle({
        radius: 30,
        borderColor: "black",
        // blue
        color: "#A7C7E7",
        label: "P3",
        fontSize: 16
    })
    return obj
}

function makeP4() {
    const obj = new Circle({
        radius: 30,
        borderColor: "black",
        // blue
        color: "#A7C7E7",
        label: "P4",
        fontSize: 16
    })
    return obj
}

function makeNet() {
    const obj = new Circle({
        radius: 30,
        borderColor: "black",
        color: "gray",
        fontSize: 16
    })

    return obj
}

function makeBall() {
    const obj = new Circle({
        radius: 10,
        borderColor: "black",
        color: "yellow",
        fontSize: 16
    })
    return obj
}

function makeBoard(stateAtom) {
    let innerGrid = new Grid({
        grid_location: {x: 0, y:0},
        cell_size: {x_size: 120, y_size: 120},
        grid_dimensions: {x_size: 3, y_size: 3 }
    })

    innerGrid.gridLines = false

    // make a rectangle that contains text boxes on the right side outside of the grid that include the state number, score, the number of touches, possession, and a rectangle if serving
    const rect = new Rectangle({
        width: 200,
        height: 400,
        borderColor: "black",
        color: "white",
        fontSize: 16
    })

    // position rect outside grid and to the right
    rect.coords = {x: 400, y: 0}

    grid.add({x: 0, y: 0}, rect)

    // add text boxes to the rectangle
    const stateNum = new TextBox({
        // text: `State: ${stateAtom.stateNum}`,
        text: "STATE",
        coords: {x: 0, y: 0},
        color: 'black',
        fontSize: 16
    })

    // for row
    for (r = 0; r <= 2; r++) {
        // for cols
        for (c = 0; c <= 2; c++) {
            // based on if ball's position is North, South, East, West, Net, or Ground, add ball (ground at 0,0)
            // print string representation of ball
            // if at 1,0 add P1 at North
            if (r == 1 && c == 0) {
                innerGrid.add({x: r, y: c}, makeP1())
            }
            // if at 0,1 add P2 at West
            if (r == 0 && c == 1) {
                innerGrid.add({x: r, y: c}, makeP2())
            }
            // if at 1,2 add P4 at South
            if (r == 1 && c == 2) {
                innerGrid.add({x: r, y: c}, makeP4())
            }
            // if at 2,1 add P4 at East
            if (r == 2 && c == 1) {
                innerGrid.add({x: r, y: c}, makeP3())
            }
            // if at 1,1 add net
            if (r == 1 && c == 1) {
                innerGrid.add({x: r, y: c}, makeNet())
            }

            if (stateAtom.ball.equals(instance.atom("North0"))) {
                innerGrid.add({x: 1, y: 0}, makeBall(ball))
            }

            else if (stateAtom.ball.equals(instance.atom("South0"))) {
                innerGrid.add({x: 1, y: 2}, makeBall(ball))
            }

            else if (stateAtom.ball.equals(instance.atom("East0"))) {
                innerGrid.add({x: 2, y: 1}, makeBall(ball))
            }

            else if (stateAtom.ball.equals(instance.atom("West0"))) {
                innerGrid.add({x: 0, y: 1}, makeBall(ball))
            }

            else if (stateAtom.ball.equals(instance.atom("Net0"))) {
                innerGrid.add({x: 1, y: 1}, makeBall(ball))
            }

            else if (stateAtom.ball.equals(instance.atom("Ground0"))) {
                innerGrid.add({x: 0, y: 0}, makeBall(ball))
            }
        }
    }

    return innerGrid
}

// render stage
stage.render(svg, document)

// resize svg
const svgContainer = document.getElementById('svg-container')
svgContainer.getElementsByTagName('svg')[0].style.height = '1950%'
svgContainer.getElementsByTagName('svg')[0].style.width = '100%'