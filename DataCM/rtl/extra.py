import re

def extract_if_condition_from_line(line):
    start = line.find("if")
    if start == -1:
        return None

    paren_start = line.find("(", start)
    if paren_start == -1:
        return None

    count = 0
    condition = ''
    for i in range(paren_start, len(line)):
        char = line[i]
        if char == '(':
            count += 1
        elif char == ')':
            count -= 1
        condition += char
        if count == 0:
            break

    if count != 0:
        return None  # 括号不匹配

    return condition[1:-1].strip()  # 去掉最外层括号

def extract_if_conditions_before_assert(lines):
    results = []

    for lineno, line in enumerate(lines, 1):
        if 'ASSERT_VERBOSE_COND_' in line:
            comment = ''
            if '//' in line:
                comment = line.split('//', 1)[1].strip()  # 提取注释部分，如路径
            for offset in [2, 1]:  # 向上两行查找
                target_lineno = lineno - offset
                if 0 <= target_lineno - 1 < len(lines):
                    prev_line = lines[target_lineno - 1]
                    condition = extract_if_condition_from_line(prev_line)
                    if condition:
                        results.append((target_lineno, condition, lineno, line.strip(), comment))
                        break
    return results

def main():
    input_file = "DataCtrlEntry.sv"
    output_file = "if_conditions_before_assert.txt"

    try:
        with open(input_file, "r") as f:
            lines = f.readlines()
    except FileNotFoundError:
        print(f"❌ 文件 {input_file} 未找到！请检查路径。")
        return

    results = extract_if_conditions_before_assert(lines)

    if not results:
        print("⚠️ 未找到任何 ASSERT_VERBOSE_COND_ 前的 if 条件。")
        return

    print("✅ 提取到的 if 条件及其对应的 ASSERT 行：\n")
    for if_lineno, cond, assert_lineno, assert_line, comment in results:
        print(f"Line {if_lineno}: {cond}")
        print(f"// {comment}\n")

    with open(output_file, "w") as f:
        for if_lineno, cond, assert_lineno, assert_line, comment in results:
            f.write(f"Line {if_lineno}: {cond}\n")
            f.write(f"// {comment}\n\n")

    print(f"✅ 已保存至：{output_file}")

if __name__ == "__main__":
    main()
