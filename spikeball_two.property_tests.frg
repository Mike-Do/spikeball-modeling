#lang forge
open "spikeball.frg"
option problem_type temporal
option max_tracelength 40

pred server_to_ground {
    // there exists some state where in the pre the is_serving flag is 1 and in the post the ball is on ground
    some pre, post: SBState {
        post = pre.next
        pre.is_serving = 1
        pre.ball = pre.serving_team.server.position 
        post.ball = Ground
    }
}


test expect {
    serverToGround: {traces implies server_to_ground} for exactly 4 Player, exactly 2 Team, 7 Int for {next is linear} is sat
}