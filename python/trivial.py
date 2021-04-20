# An trivial application that does nothing
import petr4
from petr4.runtime import *

class MyApp(petr4.App):
  pass

app = MyApp()
app.start_event_loop()
