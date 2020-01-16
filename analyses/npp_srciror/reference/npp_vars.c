#include <stdbool.h>

#define NUM 100

// TIME
int TIME = 0;

// inputs
bool the_reset_button = false;
bool old_the_reset_button = false;

bool the_blockage_button = false;
bool old_the_blockage_button = false;

int the_water_pressure = 0;
int old_the_water_pressure = 0;

// outputs
int the_safety_injection_mode = 1;
bool the_overridden_mode = false;
int the_pressure_mode = 1;
int old_the_pressure_mode = 1;

void reset() {
    TIME = 0;
    the_reset_button = false;
	old_the_reset_button = false;
	the_blockage_button = false;
	old_the_blockage_button = false;
	the_water_pressure = 0;
	old_the_water_pressure = 0;
    the_safety_injection_mode = 1;
	the_overridden_mode = false;
	the_pressure_mode = 1;
	old_the_pressure_mode = 1;
}
