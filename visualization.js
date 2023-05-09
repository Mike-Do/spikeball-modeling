// Define stage
const stage = new Stage()
const numStates = instance.signature('SBState').tuples().length

// Define outer grid
let grid = new Grid({
    grid_location: {x: 15, y: 15},
    cell_size: {x_size: 270, y_size: 270},
    grid_dimensions: {x_size: 1, y_size: numStates }
})

// create an inner 3x3 grid for each state, specify North, South, East, West on the grid, and net in the middle
for (b = 0; b <= numStates; b++) {
    // for each state, add the inner grid
    if(SBState.atom("SBState"+b) != null) {
        // on odd b, make the background rectangle white, else make it gray #D1D0CE
        let background = new Rectangle({
            width: 270,
            height: 270,
            borderColor: "black",
            color: b % 2 == 0 ? "white" : "#D1D0CE",
            coords: {x: 15, y: 15 + 270*b}
        })

        stage.add(background)

        grid.add({x:0, y:b}, makeBoard(SBState.atom("SBState"+b)))
        // for each state, add a Rectangle with the State number, score, number of touches, possession indicated by a circle with the Team color, and a text that will say which team is serving if is_serving is true
        stage.add(makeStats(SBState.atom("SBState"+b), b))
    }
}

function makeP1() {
    const obj = new Circle({
        radius: 20,
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
        radius: 20,
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
        radius: 20,
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
        radius: 20,
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
        radius: 20,
        borderColor: "black",
        color: "gray",
        fontSize: 16
    })

    return obj
}

function makeBall(stateAtom) {
    const obj = new Circle({
        radius: 10,
        borderColor: "black",
        // if stateAtom.is_serving is true, make the ball red with a thick borderWidth
        color: stateAtom.is_serving.tuples() == 1 ? "red" : "yellow",
        borderWidth: stateAtom.is_serving.tuples() == 1 ? 3 : 2,
        fontSize: 16
    })
    return obj
}

function makeBoard(stateAtom) {
    let innerGrid = new Grid({
        grid_location: {x: 0, y:0},
        cell_size: {x_size: 75, y_size: 75},
        grid_dimensions: {x_size: 3, y_size: 3 }
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
                innerGrid.add({x: 1, y: 0}, makeBall(stateAtom))
            }

            else if (stateAtom.ball.equals(instance.atom("South0"))) {
                innerGrid.add({x: 1, y: 2}, makeBall(stateAtom))
            }

            else if (stateAtom.ball.equals(instance.atom("East0"))) {
                innerGrid.add({x: 2, y: 1}, makeBall(stateAtom))
            }

            else if (stateAtom.ball.equals(instance.atom("West0"))) {
                innerGrid.add({x: 0, y: 1}, makeBall(stateAtom))
            }

            else if (stateAtom.ball.equals(instance.atom("Net0"))) {
                innerGrid.add({x: 1, y: 1}, makeBall(stateAtom))
            }

            else if (stateAtom.ball.equals(instance.atom("Ground0"))) {
                innerGrid.add({x: 0, y: 0}, makeBall(stateAtom))
            }
        }
    }

    return innerGrid
}

// for each board, on the right of the board will be a Rectangle with the State number, score, number of touches, possession, and a text that will say which team is serving if_serving is true
function makeStats(stateAtom, b) {
    // first rectangle starts at y=15, b is the state number, so the new y is 15 + 270*b
    let stats = new Grid({
        // use 20 for y to account for the margin between each rectangle
        grid_location: {x: 300, y: 20 + 270*b},
        cell_size: {x_size: 240, y_size: 52},
        grid_dimensions: {x_size: 1, y_size: 5 },
    })

    // add text for State number onto the rectangle
    let stateText = new Rectangle({
        width: 240,
        height: 52,
        label: `State ${b}`,
        borderColor: "black",
        // make color alternate, so if b is even, make it white, else make it gray
        color: b % 2 == 0 ? "white" : "#D1D0CE",
        // make label appear bolder
        labelColor: "black",
        labelSize: 18,
        // make bold
    })

    // add text for score onto the rectangle
    let team1Score = new Rectangle({
        width: 240,
        height: 52,
        label: `Team 1 Score: ${stateAtom.score[instance.atom("Team10")].tuples()}`,
        borderColor: "black",
        color: b % 2 == 0 ? "white" : "#D1D0CE",
        labelSize: 16
    })

    let team2Score = new Rectangle({
        width: 240,
        height: 52,
        label: `Team 2 Score: ${stateAtom.score[instance.atom("Team20")].tuples()}`,
        borderColor: "black",
        color: b % 2 == 0 ? "white" : "#D1D0CE",
        labelSize: 16
    })

    // add a circle with the Team color, #A7C7E7 for Team2, #FAA0A0 for Team1 and a Label that says "Team 1 Possession" or "Team 2 Possession"
    let possession = new Rectangle({
        width: 240,
        height: 52,
        borderColor: "black",
        // if Team1 is serving, make it red, else make it blue
        color: stateAtom.possession.equals(instance.atom("Team10")) ? "#FAA0A0" : "#A7C7E7",
        label: stateAtom.possession.equals(instance.atom("Team10")) ? "Team 1 Possession" : "Team 2 Possession",
        labelSize: 16
    })

    // add text for number of touches onto the rectangle
    let touches = new Rectangle({
        width: 240,
        height: 52,
        label: `Touches: ${stateAtom.num_touches.tuples()}`,
        borderColor: "black",
        color: b % 2 == 0 ? "white" : "#D1D0CE",
        labelSize: 16
    })


    stats.add({x: 0, y: 0}, stateText)
    stats.add({x: 0, y: 1}, possession)
    stats.add({x: 0, y: 2}, touches)
    stats.add({x: 0, y: 3}, team1Score)
    stats.add({x: 0, y: 4}, team2Score)
    return stats
}
stage.add(grid)

// render stage
stage.render(svg, document)

// resize svg
const svgContainer = document.getElementById('svg-container')
// NOTE: make 1100% for 40 states, and 2600% for 80 states for Spikeball 1 and Spikeball 2
svgContainer.getElementsByTagName('svg')[0].style.height = numStates == 40 ? '1100%' : '2600%'
svgContainer.getElementsByTagName('svg')[0].style.width = '100%'