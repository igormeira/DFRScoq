#include <stdbool.h>

#define NUM 100

// TIME
int TIME = 0;

// inputs
int the_voltage = 0;
int old_the_voltage = 0;

int the_turn_indicator_lever = 0;
int old_the_turn_indicator_lever = 0;

int the_emergency_flashing = 0;
int old_the_emergency_flashing = 0;

// outputs
int the_indication_lights = 2;
int old_the_indication_lights = 2;

int the_flashing_mode = 2;
int old_the_flashing_mode = 2;

// timers
int the_flashing_timer = 0;

void reset() {
    TIME = 0;
    the_voltage = 0;
	old_the_voltage = 0;

    the_turn_indicator_lever = 0;
	old_the_turn_indicator_lever = 0;

    the_emergency_flashing = 0;
	old_the_emergency_flashing = 0;

    the_indication_lights = 2;
	old_the_indication_lights = 2;

    the_flashing_mode = 2;
	old_the_flashing_mode = 2;

    the_flashing_timer = 0;
}

