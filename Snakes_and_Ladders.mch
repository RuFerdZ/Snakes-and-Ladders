/* Snakes_and_Ladders
 * Author: Rusiru
 * Creation date: 1/28/2022
 */
MACHINE
    Snakes_and_Ladders    
    
SETS
    // all game message feedbacks
    MESSAGES = {
        NEWGAME_STARTED,
        WENT_DOWN_A_SNAKE,
        WENT_UP_A_LADDER,
        THREW_HIGHER_VALUE_TO_FINISH,
        FINISHED_AND_WON,
        LANDED_ON_NORMAL_SQUARE
    }
    
CONSTANTS
    BOARD_POSITIONS,   // holds the board values from 1 to 100
    SNAKES,            // holds all the snakes in maplets of (head |-> tail)
    LADDERS,           // holds all the ladders in maplets of (bottom |-> top)
    DICE               // holds the possible dice values

PROPERTIES
    BOARD_POSITIONS <: NAT1 & BOARD_POSITIONS = 1..100 &
    SNAKES : BOARD_POSITIONS <-> BOARD_POSITIONS & 
    SNAKES = {(16 |-> 13), (31 |-> 4), (47 |-> 25), (63 |-> 60), (66 |-> 52), (97 |-> 75)} &
    LADDERS : BOARD_POSITIONS <-> BOARD_POSITIONS &
    LADDERS = {(3 |-> 39), (10 |-> 12), (27 |-> 53), (56 |-> 84), (61 |-> 99), (72 |-> 90)} &
    DICE <: NAT1 & DICE = 1..6
    
VARIABLES
    die_value,              // holds the current die value
    current_position,       // holds the current position in the board
    turns_taken,            // holds the number of turns the player had in a single game
    snakes_gone_down,       // holds the number of times the player went down a snake in a single game
    ladders_gone_up,        // holds the number of times the player went up a ladder in a single game
    squares_visited         // holds the path the player has gone throughout a single game
    
INVARIANT
    die_value : DICE \/ {0} &                 // die value is a element of DICE and also could be 0 in case new game started
    current_position : BOARD_POSITIONS &      // current position is always a value in the board positions
    turns_taken : NAT &                       // turns taken is always a natural number that can be greater than or equal to 0
    snakes_gone_down : NAT &                  // snakes gone down is always a natural number that can be greater than or equal to 0
    ladders_gone_up : NAT &                   // ladders gone up is always a natural number that can be greater than or equal to 0
    squares_visited : seq(BOARD_POSITIONS)    // squares visited is a sequence that holds the board positions the player visited
    
INITIALISATION 
    die_value, current_position, turns_taken, snakes_gone_down, ladders_gone_up, squares_visited := 0, 1, 0, 0, 0, [1]
    
OPERATIONS
    
    // make a move
    message, square <-- Move(roll_value) = 
    PRE
        // check if the value rolled is a valid Dice value and the player haven't already finished the game
        roll_value : DICE & current_position /= 100
    THEN
        // set the rolled value to the dice value
        die_value := roll_value ||
        // increment the number of turns taken
        turns_taken := succ(turns_taken) ||
        IF 
            // check if the new position is in range of the board
            (current_position + roll_value) <= 100 
        THEN
            IF 
                // check if the player has already moved to the last square, i.e. 100
                (current_position + roll_value) = 100
            THEN
                message := FINISHED_AND_WON ||
                square := (current_position + roll_value) ||
                current_position := (current_position + roll_value) ||
                squares_visited := squares_visited <- (current_position + roll_value)
            ELSE
                IF 
                    // check whether the player is not moving to a square with a snakes head or a ladders bottom
                    (current_position + roll_value) /: dom(SNAKES) & (current_position + roll_value) /: dom(LADDERS)
                THEN
                    message := LANDED_ON_NORMAL_SQUARE ||
                    squares_visited := squares_visited <- (current_position + roll_value) ||
                    current_position := (current_position + roll_value) ||
                    square := (current_position + roll_value) 
                ELSE
                    IF 
                        // check whether the user is moving to a square with a snakes head
                        (current_position + roll_value) : dom(SNAKES)
                    THEN   
                        message := WENT_DOWN_A_SNAKE ||                               
                        squares_visited := squares_visited ^  [(current_position + roll_value), SNAKES(current_position + roll_value)] || 
                        snakes_gone_down := succ(snakes_gone_down) ||
                        current_position := SNAKES(current_position + roll_value) ||
                        square := SNAKES(current_position + roll_value) 
                    ELSE 
                        // else the user will be moving to a square with a ladder's bottom
                        message := WENT_UP_A_LADDER ||
                        squares_visited := squares_visited ^  [(current_position + roll_value), LADDERS(current_position + roll_value)] ||
                        ladders_gone_up := succ(ladders_gone_up) ||
                        current_position := LADDERS(current_position + roll_value) ||
                        square := LADDERS(current_position + roll_value)                     
                    END              
                END
            END
        ELSE
            message := THREW_HIGHER_VALUE_TO_FINISH ||
            square := current_position
        END
    END;
    
    // display game statistics
    current_pos, no_of_snakes_encountered, no_of_ladders_encountered, number_of_turns_taken <-- GameStatistics =
    BEGIN
        current_pos, no_of_snakes_encountered, no_of_ladders_encountered, number_of_turns_taken := current_position, snakes_gone_down, ladders_gone_up, turns_taken
    END;
    
    // display visited squared
    visited_squares <-- VisitedSquares =
    BEGIN
        visited_squares := squares_visited
    END;
    
    // start new game
    message <-- NewGame =
    BEGIN
        die_value, current_position, turns_taken, snakes_gone_down, ladders_gone_up, squares_visited := 0, 1, 0, 0, 0, [1] ||
        message := NEWGAME_STARTED
    END
END