#include "reference/vm.c"
#define NUM_TCs 10

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define LINE_MAX 1024

void printTCstep(int new_TIME, bool new_the_coin_sensor, bool new_the_coffee_request_button,
	int expected_the_system_mode, int expected_the_coffee_machine_output, int expected_the_request_timer)
{
	printf("%d %d %d %d %d %d\n",
			new_TIME,
			new_the_coin_sensor,
			new_the_coffee_request_button,
			expected_the_system_mode,
			expected_the_coffee_machine_output,
			expected_the_request_timer		
		);
}

void printOutputs()
{
	printf("=> %d, %d\n", the_system_mode, the_coffee_machine_output);

}

void str2bool(char* str, bool *var)
{
	if (strcmp(str,"false") == 0) {
		*var = false;
	} else if (strcmp(str,"true") == 0) {
		*var = true;
	}
}

void main()
{
	// TIME
	int new_TIME;

	// inputs
	bool new_the_coin_sensor;
	bool new_the_coffee_request_button;

	// outputs
	int expected_the_system_mode;
	int expected_the_coffee_machine_output;

	// timers
	int expected_the_request_timer;

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
			str2bool(token, &new_the_coin_sensor);
			token = strtok(NULL, separator);
			str2bool(token, &new_the_coffee_request_button);
			token = strtok(NULL, separator);
			expected_the_system_mode = atoi(token);
			token = strtok(NULL, separator);
			expected_the_coffee_machine_output = atoi(token);			
			token = strtok(NULL, separator);
			expected_the_request_timer = atoi(token);

			// printTCstep(new_TIME, new_the_coin_sensor, new_the_coffee_request_button,
			// 	expected_the_system_mode, expected_the_coffee_machine_output, expected_the_request_timer);

			run(new_TIME, new_the_coin_sensor, new_the_coffee_request_button);

			// printOutputs();

			if (expected_the_system_mode != the_system_mode
				|| expected_the_coffee_machine_output != the_coffee_machine_output) {
				printf("Failed\n");

				// printf("Error in the following test step:\n");
				// printTCstep(new_TIME, new_the_coin_sensor, new_the_coffee_request_button,
				// 	expected_the_system_mode, expected_the_coffee_machine_output, expected_the_request_timer);

				// printf("Obtained outputs:\n");
				// printOutputs();

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