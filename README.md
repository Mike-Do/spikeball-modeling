 _____       _          _           _ _ 
/  ___|     (_) |      | |         | | |
\ `--. _ __  _| | _____| |__   __ _| | |
 `--. \ '_ \| | |/ / _ \ '_ \ / _` | | |
/\__/ / |_) | |   <  __/ |_) | (_| | | |
\____/| .__/|_|_|\_\___|_.__/ \__,_|_|_|
      | |                               
      |_|                               

# spikeball-modeling
A Spikeball Model written using Forge

# Assumption
States model ball from team possession to team possession.  The ball is always in the air, and the ball is always in the possession of a team.  The ball is never in the possession of a player.
Team 1 always starts with the ball, and P1 always serves
Team 2 always has P4 serve
Touches will always be 3 or under (valid)
Serves change after each point, rather than until the team loses a point
On serve, any opposing player can hit the ball (no explicit receiver)
All rallies will have the maximum number of touches (3) (avoid very long traces)

# Omitted
Cannot hit ball towards opponents
Cannot move 360 degrees
No switching positions on serve
Purple Team always serves first, and P1 serves to P4
P4 serves to P1 in post state
Serve is always valid (no hitting ground)
No infractions

