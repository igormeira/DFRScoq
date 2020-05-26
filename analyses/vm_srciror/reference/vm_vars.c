#include <stdbool.h>

#define NUM 100

// TIME
int TIME = 0;

// inputs
bool the_coin_sensor = false;
bool old_the_coin_sensor = false;

bool the_coffee_request_button = false;
bool old_the_coffee_request_button = false;

// outputs
int the_system_mode = 1;
int the_coffee_machine_output = 0;

//timers
int the_request_timer = 0;

void reset() {
    TIME = 0;
    the_coin_sensor = false;
    old_the_coin_sensor = false;
    the_coffee_request_button = false;
    old_the_coffee_request_button = false;
    the_system_mode = 1;
    the_coffee_machine_output = 0;
    the_request_timer = 0;
}

