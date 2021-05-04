# An trivial application that does nothing
import petr4
from petr4.runtime import *

class MyApp(petr4.App):
  def connected(self):
    print(f"MyApp.connected!")
    entry = Entry("t", [], "a", [])
    self.insert(entry)
    return

app = MyApp()
app.start_event_loop()
