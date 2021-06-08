import sys

solution = {
    'h1h2' : ['s1', 's3', 's2'],
    'h1h3' : ['s1', 's3', 's6'],
    'h1h4' : ['s1', 's4', 's7'],
    'h2h3' : ['s2', 's3', 's6'],
    'h2h4' : ['s2', 's4', 's7'],
    'h3h4' : ['s6', 's4', 's7']
}

def parse_file(filename, submission):
    file = open(filename, "r")
    lines = file.readlines()
    file.close()
    for s in lines:
        if s[0] == 'h':
            ss = s.split(':')
            key = ss[0]
            value = ss[1]
            key = key.replace(' ', '')
            value = value.replace('[','')
            value = value.replace(']','')
            value = value.replace("'", "")
            value = value.replace(' ', '')
            value = value.replace('\n', '')
            values = value.split(",")
            submission[key] = values

def grade_submission(submission):
    score = 0
    count = 0
    for k, v in submission.items():
        count += 1
        print(f"key is: { k }")
        print(f"value is : { v }")
        if solution[k] == v:
            score += 1
    print(f"total number of entries in submission: { count }")
    return score

def main(argv):
    submission = {}
    parse_file(argv[0], submission)
    score = grade_submission(submission)
    print(f"Scored { score } out of 6")

if __name__ == "__main__":
    main(sys.argv[1:])
