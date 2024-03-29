package test

import scala.swing.event.{ButtonClicked, EditDone}
import scala.swing._

/**
 * A GUI app to convert celsius to centigrade
 */
object CelsiusConverter extends SimpleSwingApplication {
  def top: Frame = new MainFrame {
    title = "Convert Celsius to Fahrenheit"
    val tempCelsius = new TextField
    val celsiusLabel = new Label {
      text = "Celsius"
      border = Swing.EmptyBorder(5, 5, 5, 5)
    }
    val convertButton = new Button {
      text = "Convert" //new javax.swing.ImageIcon("c:\\workspace\\gui\\images\\convert.gif")
      //border = Border.Empty(5, 5, 5, 5)
    }
    val fahrenheitLabel = new Label {
      text = "Fahrenheit     "
      border = Swing.EmptyBorder(5, 5, 5, 5)
      listenTo(convertButton, tempCelsius)

      def convert(): Unit = {
        val c = Integer.parseInt(tempCelsius.text)
        val f = c * 9 / 5 + 32
        text = "<html><font color = red>" + f + "</font> Fahrenheit</html>"
      }

      reactions += {
        case ButtonClicked(_) | EditDone(_) => convert()
      }
    }
    contents = tempCelsius
    new FlowPanel {
      contents += tempCelsius
      contents +=celsiusLabel
      contents +=convertButton
      contents +=fahrenheitLabel
      border = Swing.EmptyBorder(10, 10, 10, 10)
    }
    defaultButton = Some(convertButton)
  }
}
