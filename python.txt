import leanclient as lc
PROJECT_PATH = "/Users/nelsmartin/Lean/RL"
client = lc.LeanLSPClient(PROJECT_PATH)

file_path = "RL/MathTest.lean"
sfc = client.create_file_client(file_path)
sfc.open_file()
change = lc.DocumentContentChange(text="-- Adding a comment at the head of the file\n", start=[0, 0], end=[0, 0])
sfc.update_file(changes=[change])
print(sfc.get_file_content())


