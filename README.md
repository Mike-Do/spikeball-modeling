 _____       _ _        _           _ _ 
/  ___|     (_) |      | |         | | |
\ `--. _ __  _| | _____| |__   __ _| | |
 `--. \ '_ \| | |/ / _ \ '_ \ / _` | | |
/\__/ / |_) | |   <  __/ |_) | (_| | | |
\____/| .__/|_|_|\_\___|_.__/ \__,_|_|_|
      | |                               
      |_|                               

# spikeball-modeling
We're modeling spikeball games with 4 players and 2 teams, where each team has 2 players. The players in each team and the position of the players are static. The game ends when either team has won by receiving 2 points.
We want to explore the different Spikeball games Forge generates given the constraints and the number
of states.

# Model Design Choices 


# High-level description of Sigs and Preds
Sigs:
- <Position> (abstract); represents the possible positions the ball and the players could take
      - Net (extends Position)
      - Ground (extends Position)
      - North (extends Position)
      - South (extends Position)
      - East (extends Position)
      - West (extends Position)
- <Team> (abstract); represents the teams in the game; each team has a designated server
      - Team1 (extends Team)
      - Team2 (extends Team)
- <Player> (abstract); represents the players in the game; each player has a team and a position
      - P1 (extends Team)
      - P2 (extends Team)
      - P3 (extends Team)
      - P4 (extends Team)
- <SBState>; represents a state in the game and contains information about the current state in its fields,
such as the score, the serving team, and the ball's position.

Preds:
- <SBinitState>
- <SBValidStates>
- <SBfinalState>
- <SBvalidTransition>
- <serveTransition>
- <SBnetTransition>
- <SBgroundTransition>
- <SBrallyTransition>
- <SBfoulTransition>
- <TransitionStates>
- <SBSetup>

<SBinitState>, <SBfinalState>, <SBvalidTransition> together construct the 3 main stages of the game: the start, the transitions between states in the middle, and the final state.
Since there are several possible transition cases between states, we broke <SBvalidTransition> down to
the following transition predicates: <serveTransition>, <SBnetTransition>, <SBgroundTransition>, <SBrallyTransition>, <SBfoulTransition>. 

<SBValidStates> specifies the constraints that need to hold for a state to be valid and ensures that all states in the game are valid.

<TransitionStates> calls <SBinitState>, <SBfinalState> and <SBvalidTransition> to bring the different stages together and construct a full game.

<SBSetup> contains the static values in the game, including the positions of the players, the server on each team and players on each team.

# Assumption
- States model ball from team possession to team possession.  The ball is always in the air, and the ball is always in the possession of a team.  The ball is never in the possession of a player.
- The server on each team is static: Team 1 always has P1 serve; Team 2 always has P4 serve
- All rallies will have the maximum number of touches (3) to avoid very long traces
- If a team wins a point, they continue serving until the opposing team wins a point
- On serve, any opposing player can hit the ball (no explicit receiver)
- The winning condition is that a team has accumulated 2 points (instead of 11 points in the original game) to scale down the model

# Omitted
Cannot hit ball towards opponents
Cannot move 360 degrees
No switching positions on serve
Serve is always valid (always hits the net, no hitting ground)
No infractions

