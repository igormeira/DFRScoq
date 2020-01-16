import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Scanner;

public class renamer {
	
	private static String FILE_CONTENT = "";
	private static int MUTANTS = 229;

	public static void renameMutants(String example) {
		File[] mutantFiles = new File("mutants/").listFiles();
		int length = mutantFiles.length;

		boolean alreadyRan = false;
		for (int i=0; i<length; i++) {
			if (mutantFiles[i].getName().equals(example + "1.c")) {
				alreadyRan = true;
				break;
			}
		}

		if (alreadyRan) {
			return;
		}

		int k = 1;
		for (int i=0; i<length; i++) {
			if (!mutantFiles[i].isHidden() &&
					!mutantFiles[i].getName().equals("mutateSRC.sh") &&
					!mutantFiles[i].getName().equals(example + ".c") ) {
				File oldFile = new File("mutants/" + mutantFiles[i].getName());
				File newFile = new File("mutants/" + example + k + ".c");
				oldFile.renameTo(newFile);
				k++;
			}
		}
	}

	public static void createMainFiles(String example) {
		readFile("main.c");

		for (int i=1; i<=MUTANTS; i++) {
			String content = FILE_CONTENT.toString();
			content = content.replace("#include \"reference/" + example + ".c\"",
									  "#include \"mutants/" + example + i + ".c\"");

			writeFile(content, "main" + i + ".c");
		}
	}

	public static void createRun() {
		StringBuffer buffer = new StringBuffer();
		buffer.append("find . -name \"output.txt\" -exec rm -rf {} \\;\n");
		buffer.append("date +%s ;");

		for (int i=1; i<=MUTANTS; i++) {
			buffer.append("gcc main" + i + ".c -o main" + i + ";\n");
		}
		for (int i=1; i<=MUTANTS; i++) {
			buffer.append("./main" + i + " >> output.txt\n");
		}
		buffer.append("date +%s ;");

		String content = buffer.toString();
		writeFile(content, "run.sh");
	}

	public static void readFile(String filename) {
		try {
			File file = new File(filename);
			Scanner s = new Scanner(file);
			StringBuffer buffer = new StringBuffer();

			String line = "";			
			while (s.hasNextLine()) {
				line = s.nextLine();
				buffer.append(line + "\n");
			}

			FILE_CONTENT = buffer.toString();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}		
	}

	public static void writeFile(String content, String filename) {
		try {
			FileOutputStream fos = new FileOutputStream(filename);
			fos.write(content.getBytes());
			fos.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}	
	
	public static void main(String[] args) {
		String example = "npp";
		//renameTCs(example);
		renameMutants(example);
		createMainFiles(example);
		createRun();
	}

}
