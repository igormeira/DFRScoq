#include "vm_vars.c"

bool update()
{
    bool updated = false;

    if ((the_system_mode == 3) && 
        ((TIME - the_request_timer) >= 10) && ((TIME - the_request_timer) <= 30) &&
	((the_system_mode != 1) || (the_coffee_machine_output != 1)))
    {
        // printf("REQ004\n");
        updated = true;
        the_system_mode = 1;
        the_coffee_machine_output = 1;
    }
    else if ((old_the_coffee_request_button != true) && (the_coffee_request_button == true) &&
             (old_the_coin_sensor == false) && (the_coin_sensor == false) &&
             (the_system_mode == 0) && ((TIME - the_request_timer) > 30) &&
	     (the_system_mode != 2)) 
    {
        // printf("REQ003\n");
        updated = true;
        the_system_mode = 2;
        the_request_timer = TIME;
    }
    else if ((old_the_coin_sensor != true) && (the_coin_sensor == true) &&
             (the_system_mode == 1) && (the_system_mode != 0))
    {
        // printf("REQ001\n");
        updated = true;
        the_system_mode = 0;
        the_request_timer = TIME;
    }
    else if ((old_the_coffee_request_button != true) && (the_coffee_request_button == true) &&
             (old_the_coin_sensor == false) && (the_coin_sensor == false) &&
             (the_system_mode == 0) && ((TIME - the_request_timer) <= 30) &&
	     (the_system_mode != 3))
    {
        // printf("REQ002\n");
        updated = true;
        the_system_mode = 3;
        the_request_timer = TIME;
    }
    else if ((the_system_mode == 2) && ((TIME - the_request_timer) >= 30) && 
             ((TIME - the_request_timer) <= 50) && (the_system_mode != 1))
    {
        // printf("REQ005\n");
        updated = true;
        the_system_mode = 1;
        the_coffee_machine_output = 0;
    }

    return updated;
}

