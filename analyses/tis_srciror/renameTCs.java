import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Scanner;

public class renameTCs {

    public static void rename(String example) {
		File[] tcFiles = new File("testcases/").listFiles();
		int length = tcFiles.length;

		boolean alreadyRan = false;
		for (int i=0; i<length; i++) {
			if (tcFiles[i].getName().equals("tc1.csv")) {
				alreadyRan = true;
				break;
			}
		}

		if (alreadyRan) {
			return;
		}

		int k = 1;
		for (int i=0; i<length; i++) {
			if (!tcFiles[i].isHidden()) {
				File oldFile = new File("testcases/" + tcFiles[i].getName());
				File newFile = new File("testcases/tc" + k + ".csv");
				oldFile.renameTo(newFile);
				k++;
			}
		}
	}

    public static void main(String[] args) {
        String example = "tis";
        rename(example);
    }

}
