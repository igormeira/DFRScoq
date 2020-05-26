#include "reference/tis.c"
#define NUM_TCs 28

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LINE_MAX 1024

void printTCstep(int new_TIME, 
		int new_the_voltage, 
		int new_the_turn_indicator_lever,
		int new_the_emergency_flashig, 
		int expected_the_indication_lights, 
		int expected_the_flashing_mode, 
		int expected_the_flashing_timer)
{
	printf("%d %d %d %d %d %d %d\n",
			new_TIME,
			new_the_voltage,
			new_the_turn_indicator_lever,
			new_the_emergency_flashig,
			expected_the_indication_lights,
			expected_the_flashing_mode,
			expected_the_flashing_timer		
		);
}

void printOutputs()
{
	printf("=> %d, %d\n", the_indication_lights, the_flashing_mode);
}

void str2bool(char* str, bool *var)
{
	if (strcmp(str,"false") == 0) {
		*var = false;
	} else if (strcmp(str,"true") == 0) {
		*var = true;
	}
}


void run(int new_TIME, int new_the_voltage, int new_the_turn_indicator_lever,
	int new_the_emergency_flashing)
{
	old_the_voltage = the_voltage;
	old_the_turn_indicator_lever = the_turn_indicator_lever;
	old_the_emergency_flashing = the_emergency_flashing;

	TIME = new_TIME;
	the_voltage = new_the_voltage;
	the_turn_indicator_lever = new_the_turn_indicator_lever;
	the_emergency_flashing = new_the_emergency_flashing;

	int loops = 0;
	while (loops < NUM) {
		if (!update()) {
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
	int new_the_voltage;
	int new_the_turn_indicator_lever;
	int new_the_emergency_flashig;

	// outputs
	int expected_the_indication_lights;
	int expected_the_flashing_mode;

	// timers
	int expected_the_flashing_timer;

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
			new_the_voltage = atoi(token);

			token = strtok(NULL, separator);
			new_the_turn_indicator_lever = atoi(token);			

			token = strtok(NULL, separator);
			new_the_emergency_flashig = atoi(token);

			token = strtok(NULL, separator);
			expected_the_indication_lights = atoi(token);

			token = strtok(NULL, separator);
			expected_the_flashing_mode = atoi(token);			

			token = strtok(NULL, separator);
			expected_the_flashing_timer = atoi(token);

			 //printTCstep(new_TIME, new_the_voltage, new_the_turn_indicator_lever,
			 //	new_the_emergency_flashig, expected_the_indication_lights, 
			 // expected_the_flashing_mode, expected_the_flashing_timer);

			//printf("/==========RUN==========/");
			run(new_TIME, new_the_voltage, new_the_turn_indicator_lever,
				new_the_emergency_flashig);

			 //printOutputs();

			if ((expected_the_indication_lights != the_indication_lights)
				|| (expected_the_flashing_mode != the_flashing_mode)) {
				printf("Failed\n");

				 //printf("Error in the following test step:\n");
				 //printTCstep(new_TIME, new_the_voltage, new_the_turn_indicator_lever,
			  	 //	new_the_emergency_flashig, expected_the_indication_lights, 
				 // expected_the_flashing_mode, expected_the_flashing_timer);

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
