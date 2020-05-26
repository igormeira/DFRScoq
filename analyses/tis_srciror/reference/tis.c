#include <stdio.h>
#include "tis_vars.c"

bool update()
{
	bool updated = false;

	if ((old_the_voltage > 80) && (the_voltage <= 80)
	    && (the_indication_lights != 2))
	{
		//printf("REQ001\n");
		updated = true;		
		the_indication_lights = 2;
		the_flashing_timer = TIME;		
	}
	else if ((the_flashing_mode == 1) && (the_voltage > 80) &&
		 ((old_the_flashing_mode != 1) || (old_the_voltage <= 80))
		 && (the_indication_lights != 1))
	{
		//printf("REQ002\n");
		updated = true;		
		the_indication_lights = 1;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode == 3) && (the_voltage > 80) &&
		 ((old_the_flashing_mode != 3) || (old_the_voltage <= 80))
		 && (the_indication_lights != 3))
	{
		//printf("REQ003\n");
		updated = true;		
		the_indication_lights = 3;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode == 0) && (the_voltage > 80) &&
		 ((old_the_flashing_mode != 0) || (old_the_voltage <= 80))
		 && (the_indication_lights != 0))
	{
		//printf("REQ004\n");
		updated = true;		
		the_indication_lights = 0;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode == 2) && (the_voltage > 80)
		&& (the_indication_lights != 2))
	{
		//printf("REQ005\n");
		updated = true;		
		the_indication_lights = 2;
		the_flashing_timer = TIME;
	}
	else if (((the_indication_lights == 3) || (the_indication_lights == 1)) && 
		 (the_voltage > 80) && ((TIME - the_flashing_timer) >= 17)
		 && (the_indication_lights != 2))
	{
		//printf("REQ006\n");
		updated = true;		
		the_indication_lights = 2;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode == 1) && (the_indication_lights == 2) && 
		 (the_voltage > 80) && ((TIME - the_flashing_timer) >= 11)
		 && (the_indication_lights != 1))
	{
		//printf("REQ007\n");
		updated = true;		
		the_indication_lights = 1;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode == 3) && (the_indication_lights == 2) && 
		 (the_voltage > 80) && ((TIME - the_flashing_timer) >= 11)
		 && (the_indication_lights != 3))
	{
		//printf("REQ008\n");
		updated = true;		
		the_indication_lights = 3;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode == 0) && (the_indication_lights == 2) && 
		 (the_voltage > 80) && ((TIME - the_flashing_timer) >= 11)
		 && (the_indication_lights != 0))
	{
		//printf("REQ009\n");
		updated = true;		
		the_indication_lights = 0;
		the_flashing_timer = TIME;
	}
	else if ((the_emergency_flashing == 0) && (old_the_turn_indicator_lever != 1) &&
		 (the_turn_indicator_lever == 1)
		 && (the_flashing_mode != 1))
	{
		//printf("REQ010\n");
		updated = true;		
		the_flashing_mode = 1;
		the_flashing_timer = TIME;
	}
	else if ((the_emergency_flashing == 0) && (old_the_turn_indicator_lever != 2) && 
		 (the_turn_indicator_lever == 2)
		 && (the_flashing_mode != 3))
	{
		//printf("REQ011\n");
		updated = true;		
		the_flashing_mode = 3;
		the_flashing_timer = TIME;
	}
	else if ((old_the_emergency_flashing != 1) && (the_emergency_flashing == 1)
		 && (the_flashing_mode != 0))
	{
		//printf("REQ0012\n");
		updated = true;		
		the_flashing_mode = 0;
		the_flashing_timer = TIME;
	}
	else if ((old_the_turn_indicator_lever != 1) && (the_turn_indicator_lever == 1) &&
		 (old_the_emergency_flashing == 1) && (the_emergency_flashing == 1)
		 && (the_flashing_mode != 1))
	{
		//printf("REQ013\n");
		updated = true;		
		the_flashing_mode = 1;
		the_flashing_timer = TIME;
	}
	else if ((old_the_turn_indicator_lever != 2) && (the_turn_indicator_lever == 2) && 
		 (old_the_emergency_flashing == 1) && (the_emergency_flashing == 1)
		 && (the_flashing_mode != 3))
	{
		//printf("REQ014\n");
		updated = true;		
		the_flashing_mode = 3;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode != 0) && (old_the_turn_indicator_lever != 0) &&
		 (the_turn_indicator_lever == 0) && (old_the_emergency_flashing == 1) &&
 		 (the_emergency_flashing == 1)
		 && (the_flashing_mode != 0))
	{
		//printf("REQ015\n");
		updated = true;		
		the_flashing_mode = 0;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode != 1) && (old_the_turn_indicator_lever == 1) &&
		 (the_turn_indicator_lever == 1) && (old_the_emergency_flashing != 0) &&
		 (the_emergency_flashing == 0)
		 && (the_flashing_mode != 1))
	{
		//printf("REQ016\n");
		updated = true;		
		the_flashing_mode = 1;
		the_flashing_timer = TIME;
	}
	else if ((the_flashing_mode != 3) && (old_the_turn_indicator_lever == 2) &&
		 (the_turn_indicator_lever == 2) && (old_the_emergency_flashing != 0) &&
		 (the_emergency_flashing == 0)
		  && (the_flashing_mode != 3))
	{
		//printf("REQ017\n");
		updated = true;		
		the_flashing_mode = 3;
		the_flashing_timer = TIME;
	}

	return updated;
}

