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

bool update()
{
    bool updated = false;

    if ((the_system_mode == 3) && 
        ((TIME - the_request_timer) >= 10) && ((TIME - the_request_timer) <= 30))
    {
        // printf("REQ004\n");
        updated = true;
        the_system_mode = 1;
        the_coffee_machine_output = 1;
    }
    else if ((!(old_the_coffee_request_button == true)) && (the_coffee_request_button == true) &&
             (old_the_coin_sensor == false) && (the_coin_sensor == false) &&
             (the_system_mode == 0) && ((TIME - the_request_timer) > 30)) 
    {
        // printf("REQ003\n");
        updated = true;
        the_system_mode = 2;
        the_request_timer = TIME;
    }
    else if ((!(old_the_coin_sensor == true)) && (the_coin_sensor == true) &&
             (the_system_mode == 1))
    {
        // printf("REQ001\n");
        updated = true;
        the_system_mode = 0;
        the_request_timer = TIME;
    }
    else if ((!(old_the_coffee_request_button == true)) && (the_coffee_request_button == true) &&
             (old_the_coin_sensor == false) && (the_coin_sensor == false) &&
             (the_system_mode == 0) && ((TIME - the_request_timer) <= 0))
    {
        // printf("REQ002\n");
        updated = true;
        the_system_mode = 3;
        the_request_timer = TIME;
    }
    else if ((the_system_mode == 2) && ((TIME - the_request_timer) >= 30) && 
             ((TIME - the_request_timer) <= 50))
    {
        // printf("REQ005\n");
        updated = true;
        the_system_mode = 1;
        the_coffee_machine_output = 0;
    }

    return updated;
}

void run(int new_TIME, bool new_the_coin_sensor, bool new_the_coffee_request_button)
{
    old_the_coin_sensor = the_coin_sensor;
    old_the_coffee_request_button = the_coffee_request_button;

    TIME = new_TIME;
    the_coin_sensor = new_the_coin_sensor;
    the_coffee_request_button = new_the_coffee_request_button;

    int loops = 0;
    while (loops < NUM)
    {
        if (!update())
        {
            break;
        }
        loops++;
    }
}