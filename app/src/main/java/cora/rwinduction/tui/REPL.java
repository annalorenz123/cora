package cora.rwinduction.tui;

import java.util.Scanner;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Stream;

public class REPL {

  String quit = ":quit";

  // The interpreter reads the expression and decides... well, how to interpret it.
  Consumer<String> interpreter = expression -> {
    if (quit.equals(expression)) {
      System.exit(0);
    } else {
      System.out.println("> " + expression);
    }
  };

  public void runRepl() {

    KeyStrokeListener keyStrokeListener = new KeyStrokeListener();

    keyStrokeListener.test();

    try (Scanner scanner = new Scanner(System.in)) {

      // The supplier reads the user input.
      Supplier<String> input = () -> {
        System.out.println("> ");
        return scanner.nextLine();
      };



      Predicate<String> quitCommand = command -> quit.equalsIgnoreCase(command.trim());

      Stream.generate(input).forEach(interpreter);

    }
  }
}
