#include "reference/npp.c"
#define NUM_TCs 53

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LINE_MAX 1024

void printTCstep(int new_TIME, bool new_the_reset_button, bool new_the_blockage_button,
			int new_the_water_pressure, int expected_the_safety_injection_mode, 
			bool expected_the_overridden_mode, int expected_the_pressure_mode)
{
	printf("%d %d %d %d %d %d %d\n",
			new_TIME,
			new_the_reset_button,
			new_the_blockage_button,
			new_the_water_pressure,
			expected_the_safety_injection_mode,
			expected_the_overridden_mode,
			expected_the_pressure_mode		
		);
}

void printOutputs()
{
	printf("=> %d, %d, %d\n", the_safety_injection_mode, the_overridden_mode,
						  	  the_pressure_mode);
}

void str2bool(char* str, bool *var)
{
	if (strcmp(str,"false") == 0) {
		*var = false;
	} else if (strcmp(str,"true") == 0) {
		*var = true;
	}
}

void run(int new_TIME, bool new_the_reset_button, bool new_the_blockage_button,
	int new_the_water_pressure)
{
	old_the_reset_button = the_reset_button;
	old_the_blockage_button = the_blockage_button;
	old_the_water_pressure = the_water_pressure;
	TIME = new_TIME;
	the_reset_button = new_the_reset_button;
	the_blockage_button = new_the_blockage_button;
	the_water_pressure = new_the_water_pressure;

	int loops = 0;
	while (loops < NUM) 
	{
		bool updated = update();
		if (!updated) 
		{
			break;
		}
		loops++;
	}
}

void main()
{
	// TIME
	int new_TIME;

	// inputs
	bool new_the_reset_button;
	bool new_the_blockage_button;
	int new_the_water_pressure;

	// outputs
	int expected_the_safety_injection_mode;
	bool expected_the_overridden_mode;
	int expected_the_pressure_mode;

	char buffer[LINE_MAX];
	char *token;
	char separator[2] = ",";

	bool errorFound = false;

	for (int i=1; i<=NUM_TCs; i++) {
		char filename[100] = "testcases/tc";		
		char index[10];
		sprintf(index, "%d", i);

		strcat(filename, index);
		strcat(filename, ".csv");

		// printf("Running TC %s\n", filename);
        reset();	

		FILE *fp;		
		fp = fopen(filename, "r");
		fgets(buffer, sizeof buffer, fp);

		while (fgets(buffer, sizeof buffer, fp) != NULL)
		{
			token = strtok(buffer, separator);
			new_TIME = atoi(token);

			token = strtok(NULL, separator);
			str2bool(token, &new_the_reset_button);

			token = strtok(NULL, separator);
			str2bool(token, &new_the_blockage_button);

			token = strtok(NULL, separator);
			new_the_water_pressure = atoi(token);

			token = strtok(NULL, separator);
			expected_the_safety_injection_mode = atoi(token);
			
			token = strtok(NULL, separator);
			str2bool(token, &expected_the_overridden_mode);

			token = strtok(NULL, separator);
			expected_the_pressure_mode = atoi(token);

			// printTCstep(new_TIME, new_the_reset_button, new_the_blockage_button,
			// 	new_the_water_pressure, expected_the_safety_injection_mode, 
			//  expected_the_overridden_mode, expected_the_pressure_mode);

			//printf("?%d?", new_the_water_pressure);
			run(new_TIME, new_the_reset_button, new_the_blockage_button, new_the_water_pressure);

			// printOutputs();

			if (expected_the_safety_injection_mode != the_safety_injection_mode
				|| expected_the_overridden_mode != the_overridden_mode
				|| expected_the_pressure_mode != the_pressure_mode) {
				printf("Failed\n");

				 //printf("Error in the following test step:\n");
				 //printTCstep(new_TIME, new_the_reset_button, new_the_blockage_button,
				 //	new_the_water_pressure, expected_the_safety_injection_mode, 
				 // expected_the_overridden_mode, expected_the_pressure_mode);

				 //printf("Obtained outputs:\n");
				 //printOutputs();

				errorFound = true;
				break;
			}
		}
		
		fclose(fp);

		if (errorFound) {
			// printf("Stopping testing.\n");
			break;
		}
	}

	if (!errorFound) {
		printf("Passed\n");	
	}
}
