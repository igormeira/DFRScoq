#include <stdio.h>
#include "npp_vars.c"

bool update()
{
	bool updated = false;

	//printf("%d - %d - %d", the_pressure_mode, old_the_water_pressure, the_water_pressure);

	if ((the_pressure_mode == 1) && (old_the_water_pressure < 9) &&
		(the_water_pressure >= 9) && (the_pressure_mode != 2))
	{
		//printf("REQ001\n");
		updated = true;
		the_pressure_mode = 2;
	}
	else if ((the_pressure_mode == 2) && (old_the_water_pressure < 10) &&
		 (the_water_pressure >= 10) && (the_pressure_mode != 0))
	{
		//printf("REQ002\n");
		updated = true;
		the_pressure_mode = 0;
	}
	else if ((the_pressure_mode == 2) && (old_the_water_pressure >= 9) &&
		 (the_water_pressure < 9) && (the_pressure_mode != 1))
	{
		//printf("REQ003\n");
		updated = true;
		the_pressure_mode = 1;
	}
	else if ((the_pressure_mode == 0) && (old_the_water_pressure >= 10) &&
		 (the_water_pressure < 10) && (the_pressure_mode != 2))
	{
		//printf("REQ004\n");
		updated = true;
		the_pressure_mode = 2;
	}
	else if ((the_pressure_mode != 0) && (the_reset_button != true) &&
		 (old_the_blockage_button != true) && (the_blockage_button == true)
		  && (the_overridden_mode != true))
	{
		//printf("REQ005\n");
		updated = true;
		the_overridden_mode = true;
	}
	else if ((the_pressure_mode != 0) && (old_the_reset_button != true) &&
	   	 (the_reset_button == true) && (the_overridden_mode != false))
	{
		//printf("REQ006\n");
		updated = true;
		the_overridden_mode = false;
	}
	else if ((old_the_pressure_mode != 0) && (the_pressure_mode == 0)
		 && (the_overridden_mode != false))
	{
		//printf("REQ007\n");
		updated = true;
		the_overridden_mode = false;
	}
	else if ((the_pressure_mode != 0) && (old_the_pressure_mode == 0)
		 && (the_overridden_mode != false))
	{
		//printf("REQ008\n");
		updated = true;
		the_overridden_mode = false;
	}
	else if ((the_overridden_mode == true) && (the_pressure_mode == 1)
		 && (the_safety_injection_mode != 0))
	{
		//printf("REQ009\n");
		updated = true;
		the_safety_injection_mode = 0;
	}
	else if ((the_overridden_mode == false) && (the_pressure_mode == 1)
		 && (the_safety_injection_mode != 1))
	{
		//printf("REQ010\n");
		updated = true;
		the_safety_injection_mode = 1;
	}
	else if (((the_pressure_mode == 0) || (the_pressure_mode == 2))
		 && (the_safety_injection_mode != 0))
	{
		//printf("REQ011\n");
		updated = true;
		the_safety_injection_mode = 0;
	}

	return updated;
}

