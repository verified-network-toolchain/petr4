# An trivial application that does nothing
import petr4
from petr4.runtime import *

class MyApp(petr4.App):
  def switch_up(self,switch,ports):
    print(f"MyApp.switch_up { switch }!")
    entry = Entry("t", [], "a", [])
    self.insert(switch, entry)
    return

app = MyApp()
app.start()
