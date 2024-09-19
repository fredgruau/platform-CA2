package simulator
import scala.swing._
class TestButtonSwing {
}
object TestButtonSwing {

  def main(args: Array[String]) {

    new Frame {
      title = "Hello world"

      contents = new FlowPanel {
        contents += new Label("Launch rainbows:")
        contents += new Button("Click me") {
          reactions += {
            case event.ButtonClicked(_) =>
              println("All the colours!")
          }
        }
      }

      pack()
      centerOnScreen()
      open()
    }
  }
}
